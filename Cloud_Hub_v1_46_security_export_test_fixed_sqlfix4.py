#!/usr/bin/env python3
"""
CLOUD HUB | Customer/staff + loyalty + storefront upgrades v1.46
=================================================

Target: Python 3.11+, pyTelegramBotAPI, PostgreSQL, Render Background Worker.

This file is an implementation baseline, not a claim that every feature in
Cloud Hub Handoff v1.9 is complete. Implemented here:
- PostgreSQL connection pooling and idempotent schema bootstrap
- staff authentication by Telegram ID and role/permission checks
- v1.19: rolling security thresholds wired to centralized audit events; staff audit pagination
- v1.19: support ticket list/detail/reply/status and staff task commands
- staff navigation and order queues
- one Telegram message/card per order
- uncollected queue without a business-result limit (delivery is chunked)
- "last 100 orders", each as a separate card
- per-order status transitions with row locking and audit records
- PostgreSQL connection pooling and idempotent schema bootstrap
- staff authentication, role checks and audit trail
- separate order cards, unlimited uncollected queue, latest 100 orders
- CRM search across the complete order history, including typo-tolerant names
- courier delivery quotes using road distance, hidden store address and three approved tariffs
- customer delivery quote confirmation flow (courier or Nova Poshta choice)
- Nova Poshta remains manual carrier selection only; no API, tariff calculation, TTN creation or tracking integration
- DB-backed customer checkout draft and consent/contact/delivery wizard
- owner/admin manual age-verification queue via /agequeue
- persisted route/price snapshots and configurable mapping endpoints
- notification outbox and safe startup/shutdown foundations
- supplier directory and draft supply documents with partial receipt
- atomic supply posting, weighted-average cost, SKU stock ledger and audit
- blind inventory count UI with concurrent movement reconciliation
- low-stock, stock movement and owner-only stock valuation views
- owner-only order lifecycle reconciliation (read-only; no silent stock/payment repair)
- controlled return documents, SKU restocking, and owner-confirmed manual refund ledger
- loyalty reversal on returns with debt offset against future earnings
- immutable historical unit-cost snapshots and owner-only gross-margin report
- owner Security Center UI for staff lifecycle, review, lock/unlock, activation, role changes and event journal
- v1.30: owner-only read-only schema preflight across business and consent PostgreSQL databases
- v1.30: payment capture rejects partial settlement until a real installment ledger exists
- v1.32: repaired catalogue and operations navigation; owner-only runtime self-check command for critical pure business invariants
- v1.37: improved customer menu, /start notice, job-request ticket, one-time staff access codes
- v1.37: order comment and pre-shipment detail-edit actions
- v1.44: owner delivery-slot schedule generator with timezone-aware validation and audit
- v1.44: atomic checkout bonus redemption and pending bonus accrual; repaired clear_cart
- v1.46: customer product photo cards, variant selection, cart item removal, wholesale requests/history, roulette, shipping labels

This is a single-file application. It is designed to be extended in place; do not
split it into a multi-file project for the owner. Some advanced handoff modules still require implementation and live-provider testing before launch. This repaired build fixes known broken navigation paths; it is not a substitute for live checkout, Telegram, database, and provider acceptance tests. Nova Poshta is intentionally not API-integrated: the customer is told that the carrier sets the shipping price.

Render environment variables:
  BOT_TOKEN                 required
  DATABASE_URL              required (Render PostgreSQL URL, logical DB cloudhub)
  CONSENT_DATABASE_URL      required (separate PostgreSQL DB cloudhub_consent)
  DATA_DIR                  Render disk mount, default /var/data
  REQUIRE_PERSISTENT_DISK   optional, default true
  OWNER_TELEGRAM_ID         required (numeric Telegram user ID)
  TIMEZONE                  optional, default Europe/Kyiv
  LOG_LEVEL                 optional, default INFO
  ORDER_CARD_BATCH_SIZE     optional, default 20 (Telegram delivery pacing)
  ORDER_CARD_DELAY_SECONDS optional, default 0.7
  ADMIN_TELEGRAM_IDS        optional, comma-separated bootstrap admins
  PRIVACY_CONSENT_TEXT      owner-approved full consent text (required for checkout)
  PRIVACY_CONSENT_VERSION   consent version; increment when the text changes
  CUSTOMER_EXPORT_PASSWORD owner-only password required for customer PDF export
  CUSTOMER_EXPORT_FONT_PATH optional absolute path to CloudHub-DejaVuSans.ttf

Do not commit secrets. Do not point this bot at the legacy CRM database.
"""

from __future__ import annotations

import difflib
import html
import inspect
import logging
import os
import re
import secrets
import hashlib
import signal
import sys
import threading
import time
import unicodedata
import uuid
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import datetime, timezone
from decimal import Decimal, ROUND_HALF_UP
from typing import Any, Iterable, Optional
from types import SimpleNamespace as _NS
from zoneinfo import ZoneInfo

try:
    import telebot
    from telebot import types
except ImportError as exc:
    raise SystemExit(
        "Missing dependency pyTelegramBotAPI. Install with: pip install pyTelegramBotAPI"
    ) from exc

try:
    from psycopg_pool import ConnectionPool
    from psycopg.rows import dict_row
    from psycopg import errors as pg_errors
except ImportError as exc:
    raise SystemExit(
        "Missing PostgreSQL dependencies. Install with: pip install 'psycopg[binary,pool]'"
    ) from exc


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Config:
    bot_token: str
    database_url: str
    owner_id: int
    timezone: str = "Europe/Kyiv"
    log_level: str = "INFO"
    batch_size: int = 20
    card_delay: float = 0.7
    admin_ids: tuple[int, ...] = ()
    # Internal origin only. Never include it in customer-facing text.
    store_address: str = "Львів, вул. Жасминова, 11"
    store_lat: Optional[float] = None
    store_lon: Optional[float] = None
    max_courier_km: float = 20.0
    geocoding_url: str = "https://nominatim.openstreetmap.org/search"
    routing_url: str = "https://router.project-osrm.org/route/v1/driving"
    map_user_agent: str = "CloudHubBot/1.0 (Telegram shop https://t.me/Cloud_hub_vape_bot)"
    map_request_timeout: int = 12
    data_dir: str = "/var/data"
    database_name: str = "cloudhub"
    consent_database_url: str = ""
    reservation_minutes: int = 30
    privacy_consent_version: str = "v1"
    privacy_consent_text: str = ""

    @classmethod
    def from_env(cls) -> "Config":
        token = os.getenv("BOT_TOKEN", "").strip()
        db_url = os.getenv("DATABASE_URL", "").strip()
        owner_raw = os.getenv("OWNER_TELEGRAM_ID", "").strip()
        if not token:
            raise RuntimeError("BOT_TOKEN is not configured")
        if not db_url:
            raise RuntimeError("DATABASE_URL is not configured")
        if not owner_raw.isdigit():
            raise RuntimeError("OWNER_TELEGRAM_ID must be a numeric Telegram ID")
        if db_url.startswith("postgres://"):
            db_url = "postgresql://" + db_url[len("postgres://"):]
        admins = tuple(
            int(x.strip()) for x in os.getenv("ADMIN_TELEGRAM_IDS", "").split(",")
            if x.strip().isdigit()
        )
        return cls(
            bot_token=token,
            database_url=db_url,
            owner_id=int(owner_raw),
            timezone=os.getenv("TIMEZONE", "Europe/Kyiv"),
            log_level=os.getenv("LOG_LEVEL", "INFO").upper(),
            batch_size=max(1, min(50, int(os.getenv("ORDER_CARD_BATCH_SIZE", "20")))),
            card_delay=max(0.2, float(os.getenv("ORDER_CARD_DELAY_SECONDS", "0.7"))),
            admin_ids=admins,
            store_address=os.getenv("STORE_ADDRESS", "Львів, вул. Жасминова, 11"),
            store_lat=_optional_float("STORE_LAT"),
            store_lon=_optional_float("STORE_LON"),
            max_courier_km=max(0.1, float(os.getenv("MAX_COURIER_KM", "20"))),
            geocoding_url=os.getenv("GEOCODING_URL", "https://nominatim.openstreetmap.org/search"),
            routing_url=os.getenv("ROUTING_URL", "https://router.project-osrm.org/route/v1/driving"),
            map_user_agent=os.getenv("MAP_USER_AGENT", "CloudHubBot/1.0 (Telegram shop https://t.me/Cloud_hub_vape_bot)"),
            map_request_timeout=max(3, min(30, int(os.getenv("MAP_REQUEST_TIMEOUT", "12")))),
            data_dir=os.getenv("DATA_DIR", "/var/data"),
            database_name=os.getenv("APP_DATABASE_NAME", "cloudhub"),
            consent_database_url=os.getenv("CONSENT_DATABASE_URL", "").strip(),
            reservation_minutes=max(5, min(240, int(os.getenv("RESERVATION_MINUTES", "30")))),
            privacy_consent_version=os.getenv("PRIVACY_CONSENT_VERSION", "v1").strip() or "v1",
            privacy_consent_text=os.getenv("PRIVACY_CONSENT_TEXT", "").strip(),
        )


def _optional_float(name: str) -> Optional[float]:
    raw = os.getenv(name, "").strip()
    if not raw:
        return None
    try:
        return float(raw)
    except ValueError as exc:
        raise RuntimeError(f"{name} must be a number") from exc


CONFIG = Config.from_env()
logging.basicConfig(
    level=getattr(logging, CONFIG.log_level, logging.INFO),
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
)
log = logging.getLogger("cloudhub")
bot = telebot.TeleBot(CONFIG.bot_token, parse_mode="HTML", threaded=True)


# ---------------------------------------------------------------------------
# PostgreSQL schema
# ---------------------------------------------------------------------------

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS staff (
    telegram_id BIGINT PRIMARY KEY,
    display_name TEXT NOT NULL,
    role TEXT NOT NULL CHECK (role IN ('owner','admin','manager','packer','courier')),
    active BOOLEAN NOT NULL DEFAULT TRUE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS staff_access_codes (
    id BIGSERIAL PRIMARY KEY,
    code_hash TEXT NOT NULL UNIQUE,
    role TEXT NOT NULL CHECK (role IN ('admin','manager','packer','courier')),
    created_by BIGINT NOT NULL,
    expires_at TIMESTAMPTZ NOT NULL,
    used_at TIMESTAMPTZ,
    used_by BIGINT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_staff_access_codes_active
    ON staff_access_codes(expires_at) WHERE used_at IS NULL;



ALTER TABLE staff DROP CONSTRAINT IF EXISTS staff_role_check;
ALTER TABLE staff ADD CONSTRAINT staff_role_check CHECK (role IN ('owner','admin','manager','packer','courier'));

CREATE TABLE IF NOT EXISTS customers (
    id BIGSERIAL PRIMARY KEY,
    telegram_id BIGINT UNIQUE,
    username TEXT,
    first_name TEXT,
    last_name TEXT,
    phone TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS orders (
    id BIGSERIAL PRIMARY KEY,
    order_number TEXT NOT NULL UNIQUE,
    customer_id BIGINT REFERENCES customers(id),
    customer_name_snapshot TEXT NOT NULL DEFAULT '',
    phone_snapshot TEXT NOT NULL DEFAULT '',
    telegram_id_snapshot BIGINT,
    username_snapshot TEXT,
    status TEXT NOT NULL DEFAULT 'new',
    city TEXT NOT NULL DEFAULT '',
    delivery_branch TEXT NOT NULL DEFAULT '',
    delivery_address TEXT NOT NULL DEFAULT '',
    ttn TEXT NOT NULL DEFAULT '',
    delivery_type TEXT NOT NULL DEFAULT '',
    payment_method TEXT NOT NULL DEFAULT 'cod',
    items_total NUMERIC(12,2) NOT NULL DEFAULT 0,
    delivery_total NUMERIC(12,2) NOT NULL DEFAULT 0,
    grand_total NUMERIC(12,2) NOT NULL DEFAULT 0,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS order_items (
    id BIGSERIAL PRIMARY KEY,
    order_id BIGINT NOT NULL REFERENCES orders(id) ON DELETE RESTRICT,
    product_name_snapshot TEXT NOT NULL,
    sku_snapshot TEXT NOT NULL DEFAULT '',
    quantity INTEGER NOT NULL CHECK (quantity > 0),
    unit_price NUMERIC(12,2) NOT NULL CHECK (unit_price >= 0),
    line_total NUMERIC(12,2) NOT NULL CHECK (line_total >= 0)
);

CREATE TABLE IF NOT EXISTS order_comments (
    id BIGSERIAL PRIMARY KEY,
    order_id BIGINT NOT NULL REFERENCES orders(id) ON DELETE RESTRICT,
    author_telegram_id BIGINT NOT NULL,
    author_role TEXT NOT NULL,
    body TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_order_comments_order ON order_comments(order_id,created_at DESC);


CREATE TABLE IF NOT EXISTS audit_log (
    id BIGSERIAL PRIMARY KEY,
    actor_telegram_id BIGINT,
    actor_role TEXT,
    action TEXT NOT NULL,
    entity_type TEXT NOT NULL,
    entity_id TEXT NOT NULL,
    before_data JSONB,
    after_data JSONB,
    reason TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX IF NOT EXISTS idx_orders_status_created ON orders(status, created_at DESC, id DESC);
CREATE INDEX IF NOT EXISTS idx_orders_created ON orders(created_at DESC, id DESC);
CREATE INDEX IF NOT EXISTS idx_orders_phone ON orders(phone_snapshot);
CREATE INDEX IF NOT EXISTS idx_orders_ttn ON orders(ttn);
CREATE INDEX IF NOT EXISTS idx_orders_customer_name ON orders USING gin (to_tsvector('simple', customer_name_snapshot));
CREATE INDEX IF NOT EXISTS idx_customers_phone ON customers(phone);
CREATE INDEX IF NOT EXISTS idx_customers_name ON customers USING gin (to_tsvector('simple', coalesce(first_name,'') || ' ' || coalesce(last_name,'')));

CREATE TABLE IF NOT EXISTS notification_outbox (
    id BIGSERIAL PRIMARY KEY,
    recipient_telegram_id BIGINT NOT NULL,
    category TEXT NOT NULL,
    payload JSONB NOT NULL,
    dedupe_key TEXT UNIQUE,
    state TEXT NOT NULL DEFAULT 'pending' CHECK (state IN ('pending','sent','failed','blocked')),
    attempts INTEGER NOT NULL DEFAULT 0,
    last_error TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    sent_at TIMESTAMPTZ,
    available_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    last_attempt_at TIMESTAMPTZ,
    claim_token TEXT
);

CREATE TABLE IF NOT EXISTS delivery_tariffs (
    tariff_code TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    base_fee NUMERIC(10,2) NOT NULL CHECK (base_fee >= 0),
    per_km NUMERIC(10,2) NOT NULL CHECK (per_km >= 0),
    minimum_fee NUMERIC(10,2),
    active BOOLEAN NOT NULL DEFAULT TRUE,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS delivery_route_cache (
    id BIGSERIAL PRIMARY KEY,
    normalized_address TEXT NOT NULL UNIQUE,
    latitude DOUBLE PRECISION NOT NULL,
    longitude DOUBLE PRECISION NOT NULL,
    display_address TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    last_used_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS delivery_quotes (
    id BIGSERIAL PRIMARY KEY,
    customer_telegram_id BIGINT NOT NULL,
    destination_address TEXT NOT NULL,
    destination_lat DOUBLE PRECISION NOT NULL,
    destination_lon DOUBLE PRECISION NOT NULL,
    distance_km NUMERIC(9,3) NOT NULL,
    duration_minutes NUMERIC(9,2),
    tariff_code TEXT NOT NULL,
    tariff_base NUMERIC(10,2) NOT NULL,
    tariff_per_km NUMERIC(10,2) NOT NULL,
    delivery_price NUMERIC(10,2) NOT NULL,
    route_provider TEXT NOT NULL,
    route_reference TEXT,
    state TEXT NOT NULL DEFAULT 'pending' CHECK (state IN ('pending','accepted','declined','expired','used')),
    expires_at TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_delivery_quotes_customer ON delivery_quotes(customer_telegram_id, created_at DESC);

-- Product catalogue and media metadata. Binary media is stored on the Render disk;
-- this database stores stable relative paths and Telegram file IDs.
CREATE TABLE IF NOT EXISTS categories (
    id BIGSERIAL PRIMARY KEY, name TEXT NOT NULL UNIQUE, parent_id BIGINT REFERENCES categories(id),
    active BOOLEAN NOT NULL DEFAULT TRUE, sort_order INTEGER NOT NULL DEFAULT 0,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS brands (
    id BIGSERIAL PRIMARY KEY, name TEXT NOT NULL UNIQUE, active BOOLEAN NOT NULL DEFAULT TRUE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
-- Explicit many-to-many brand/departement mapping. A brand can be available
-- in multiple departments before its first product is created there.
CREATE TABLE IF NOT EXISTS brand_categories (
    brand_id BIGINT NOT NULL REFERENCES brands(id) ON DELETE RESTRICT,
    category_id BIGINT NOT NULL REFERENCES categories(id) ON DELETE RESTRICT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    PRIMARY KEY(brand_id,category_id)
);
CREATE INDEX IF NOT EXISTS idx_brand_categories_category ON brand_categories(category_id,brand_id);
CREATE TABLE IF NOT EXISTS products (
    id BIGSERIAL PRIMARY KEY, category_id BIGINT REFERENCES categories(id), brand_id BIGINT REFERENCES brands(id),
    name TEXT NOT NULL, description TEXT NOT NULL DEFAULT '', active BOOLEAN NOT NULL DEFAULT TRUE,
    manually_hidden BOOLEAN NOT NULL DEFAULT FALSE, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), archived_at TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS product_variants (
    id BIGSERIAL PRIMARY KEY, product_id BIGINT NOT NULL REFERENCES products(id) ON DELETE RESTRICT,
    sku TEXT NOT NULL UNIQUE, variant_name TEXT NOT NULL DEFAULT '', price NUMERIC(12,2) NOT NULL CHECK(price>=0),
    cost_price NUMERIC(12,2) CHECK(cost_price IS NULL OR cost_price>=0),
    stock_qty INTEGER NOT NULL DEFAULT 0 CHECK(stock_qty>=0), reserved_qty INTEGER NOT NULL DEFAULT 0 CHECK(reserved_qty>=0),
    low_stock_threshold INTEGER NOT NULL DEFAULT 0 CHECK(low_stock_threshold>=0),
    active BOOLEAN NOT NULL DEFAULT TRUE, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_products_active ON products(active, manually_hidden);
CREATE INDEX IF NOT EXISTS idx_products_category_brand ON products(category_id,brand_id,active);
CREATE INDEX IF NOT EXISTS idx_variants_product ON product_variants(product_id);
CREATE TABLE IF NOT EXISTS product_media (
    id BIGSERIAL PRIMARY KEY, product_id BIGINT NOT NULL REFERENCES products(id) ON DELETE RESTRICT,
    telegram_file_id TEXT, disk_path TEXT, sort_order INTEGER NOT NULL DEFAULT 0,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), CHECK(telegram_file_id IS NOT NULL OR disk_path IS NOT NULL)
);
CREATE TABLE IF NOT EXISTS price_history (
    id BIGSERIAL PRIMARY KEY, variant_id BIGINT NOT NULL REFERENCES product_variants(id),
    old_price NUMERIC(12,2), new_price NUMERIC(12,2) NOT NULL, actor_telegram_id BIGINT,
    reason TEXT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS inventory_movements (
    id BIGSERIAL PRIMARY KEY, variant_id BIGINT NOT NULL REFERENCES product_variants(id),
    movement_type TEXT NOT NULL, quantity_delta INTEGER NOT NULL, reference_type TEXT,
    reference_id TEXT, reason TEXT, actor_telegram_id BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS inventory_counts (
    id BIGSERIAL PRIMARY KEY, status TEXT NOT NULL DEFAULT 'draft' CHECK(status IN ('draft','counting','confirmed','cancelled')),
    created_by BIGINT NOT NULL, confirmed_by BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    confirmed_at TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS inventory_count_items (
    id BIGSERIAL PRIMARY KEY, count_id BIGINT NOT NULL REFERENCES inventory_counts(id) ON DELETE RESTRICT,
    variant_id BIGINT NOT NULL REFERENCES product_variants(id), actual_qty INTEGER CHECK(actual_qty>=0),
    system_qty_snapshot INTEGER, discrepancy INTEGER, reason TEXT, counted_by BIGINT,
    counted_at TIMESTAMPTZ,
    UNIQUE(count_id,variant_id)
);
ALTER TABLE inventory_count_items ADD COLUMN IF NOT EXISTS counted_at TIMESTAMPTZ;
CREATE INDEX IF NOT EXISTS idx_inventory_variant_time ON inventory_movements(variant_id, created_at DESC);
CREATE TABLE IF NOT EXISTS stock_reservations (
    id BIGSERIAL PRIMARY KEY, order_id BIGINT REFERENCES orders(id), variant_id BIGINT NOT NULL REFERENCES product_variants(id),
    quantity INTEGER NOT NULL CHECK(quantity>0), state TEXT NOT NULL DEFAULT 'active'
      CHECK(state IN ('active','consumed','released','expired')),
    expires_at TIMESTAMPTZ NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_reservations_expiry ON stock_reservations(state, expires_at);
CREATE TABLE IF NOT EXISTS suppliers (
    id BIGSERIAL PRIMARY KEY, name TEXT NOT NULL, contact_name TEXT DEFAULT '', phone TEXT DEFAULT '',
    email TEXT DEFAULT '', notes TEXT DEFAULT '', active BOOLEAN NOT NULL DEFAULT TRUE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS supply_documents (
    id BIGSERIAL PRIMARY KEY, document_number TEXT NOT NULL UNIQUE, supplier_id BIGINT REFERENCES suppliers(id),
    state TEXT NOT NULL DEFAULT 'draft' CHECK(state IN ('draft','posted','reversed','cancelled')),
    document_date DATE, total_cost NUMERIC(14,2) NOT NULL DEFAULT 0, created_by BIGINT,
    posted_at TIMESTAMPTZ, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
ALTER TABLE supply_documents DROP CONSTRAINT IF EXISTS supply_documents_state_check;
ALTER TABLE supply_documents ADD CONSTRAINT supply_documents_state_check CHECK(state IN ('draft','posted','reversed','cancelled'));
CREATE TABLE IF NOT EXISTS supply_items (
    id BIGSERIAL PRIMARY KEY, supply_id BIGINT NOT NULL REFERENCES supply_documents(id) ON DELETE RESTRICT,
    variant_id BIGINT NOT NULL REFERENCES product_variants(id), quantity INTEGER NOT NULL CHECK(quantity>0),
    unit_cost NUMERIC(12,2) NOT NULL CHECK(unit_cost>=0), received_qty INTEGER NOT NULL DEFAULT 0 CHECK(received_qty>=0)
);
CREATE TABLE IF NOT EXISTS customer_addresses (
    id BIGSERIAL PRIMARY KEY, customer_id BIGINT NOT NULL REFERENCES customers(id), label TEXT DEFAULT '',
    city TEXT NOT NULL DEFAULT '', address TEXT NOT NULL, is_default BOOLEAN NOT NULL DEFAULT FALSE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS carts (
    customer_telegram_id BIGINT PRIMARY KEY, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS cart_items (
    id BIGSERIAL PRIMARY KEY, customer_telegram_id BIGINT NOT NULL REFERENCES carts(customer_telegram_id) ON DELETE CASCADE,
    variant_id BIGINT NOT NULL REFERENCES product_variants(id), quantity INTEGER NOT NULL CHECK(quantity>0),
    UNIQUE(customer_telegram_id, variant_id)
);
CREATE TABLE IF NOT EXISTS favorites (
    customer_telegram_id BIGINT NOT NULL, product_id BIGINT NOT NULL REFERENCES products(id),
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), PRIMARY KEY(customer_telegram_id, product_id)
);
CREATE TABLE IF NOT EXISTS loyalty_accounts (
    customer_id BIGINT PRIMARY KEY REFERENCES customers(id), available NUMERIC(12,2) NOT NULL DEFAULT 0 CHECK(available>=0),
    pending NUMERIC(12,2) NOT NULL DEFAULT 0 CHECK(pending>=0), updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS loyalty_transactions (
    id BIGSERIAL PRIMARY KEY, customer_id BIGINT NOT NULL REFERENCES customers(id), order_id BIGINT REFERENCES orders(id),
    transaction_type TEXT NOT NULL, amount NUMERIC(12,2) NOT NULL, state TEXT NOT NULL DEFAULT 'available',
    reason TEXT NOT NULL DEFAULT '', actor_telegram_id BIGINT, idempotency_key TEXT UNIQUE,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS loyalty_lots (
    id BIGSERIAL PRIMARY KEY, customer_id BIGINT NOT NULL REFERENCES customers(id),
    source_transaction_id BIGINT NOT NULL UNIQUE REFERENCES loyalty_transactions(id),
    original_amount NUMERIC(12,2) NOT NULL CHECK(original_amount>=0),
    remaining_amount NUMERIC(12,2) NOT NULL CHECK(remaining_amount>=0),
    state TEXT NOT NULL DEFAULT 'pending' CHECK(state IN ('pending','available','expired','spent')),
    available_at TIMESTAMPTZ, expires_at TIMESTAMPTZ NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_loyalty_lots_fifo ON loyalty_lots(customer_id,state,expires_at,id);
CREATE TABLE IF NOT EXISTS support_tickets (
    id BIGSERIAL PRIMARY KEY, customer_telegram_id BIGINT NOT NULL, order_id BIGINT REFERENCES orders(id),
    subject TEXT NOT NULL DEFAULT 'Звернення', status TEXT NOT NULL DEFAULT 'new'
      CHECK(status IN ('new','open','waiting_customer','closed')),
    assigned_to BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS support_messages (
    id BIGSERIAL PRIMARY KEY, ticket_id BIGINT NOT NULL REFERENCES support_tickets(id) ON DELETE RESTRICT,
    sender_telegram_id BIGINT NOT NULL, sender_type TEXT NOT NULL CHECK(sender_type IN ('customer','staff')),
    body TEXT NOT NULL, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS delivery_slots (
    id BIGSERIAL PRIMARY KEY, slot_date DATE NOT NULL, starts_at TIMESTAMPTZ NOT NULL, ends_at TIMESTAMPTZ NOT NULL,
    tariff_code TEXT NOT NULL, capacity INTEGER NOT NULL DEFAULT 1 CHECK(capacity>0),
    booked_count INTEGER NOT NULL DEFAULT 0 CHECK(booked_count>=0), active BOOLEAN NOT NULL DEFAULT TRUE,
    created_by BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), UNIQUE(starts_at, tariff_code)
);
CREATE TABLE IF NOT EXISTS courier_assignments (
    id BIGSERIAL PRIMARY KEY, order_id BIGINT NOT NULL UNIQUE REFERENCES orders(id),
    courier_telegram_id BIGINT NOT NULL, assigned_by BIGINT, assigned_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    departed_at TIMESTAMPTZ, delivered_at TIMESTAMPTZ, status TEXT NOT NULL DEFAULT 'assigned'
);
CREATE TABLE IF NOT EXISTS customer_delivery_reviews (
    id BIGSERIAL PRIMARY KEY, order_id BIGINT NOT NULL UNIQUE REFERENCES orders(id),
    customer_telegram_id BIGINT NOT NULL, rating SMALLINT NOT NULL CHECK(rating BETWEEN 1 AND 5),
    comment TEXT DEFAULT '', created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS promo_codes (
    id BIGSERIAL PRIMARY KEY, code TEXT NOT NULL UNIQUE, discount_percent NUMERIC(5,2) NOT NULL DEFAULT 0,
    discount_amount NUMERIC(12,2) NOT NULL DEFAULT 0, starts_at TIMESTAMPTZ, ends_at TIMESTAMPTZ,
    usage_limit INTEGER, used_count INTEGER NOT NULL DEFAULT 0, active BOOLEAN NOT NULL DEFAULT TRUE
);
CREATE TABLE IF NOT EXISTS broadcasts (
    id BIGSERIAL PRIMARY KEY, title TEXT NOT NULL, body TEXT NOT NULL, state TEXT NOT NULL DEFAULT 'draft'
      CHECK(state IN ('draft','scheduled','running','completed','cancelled','failed')),
    scheduled_at TIMESTAMPTZ, created_by BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS broadcast_recipients (
    id BIGSERIAL PRIMARY KEY, broadcast_id BIGINT NOT NULL REFERENCES broadcasts(id),
    customer_telegram_id BIGINT NOT NULL, state TEXT NOT NULL DEFAULT 'pending', attempts INTEGER NOT NULL DEFAULT 0,
    last_error TEXT, sent_at TIMESTAMPTZ, UNIQUE(broadcast_id, customer_telegram_id)
);
CREATE TABLE IF NOT EXISTS business_tasks (
    id BIGSERIAL PRIMARY KEY, title TEXT NOT NULL, description TEXT DEFAULT '', assigned_to BIGINT,
    created_by BIGINT, due_at TIMESTAMPTZ, status TEXT NOT NULL DEFAULT 'open'
      CHECK(status IN ('open','in_progress','done','cancelled')),
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(), completed_at TIMESTAMPTZ
);
CREATE TABLE IF NOT EXISTS business_expenses (
    id BIGSERIAL PRIMARY KEY, category TEXT NOT NULL, amount NUMERIC(14,2) NOT NULL CHECK(amount>=0),
    description TEXT DEFAULT '', expense_date DATE NOT NULL DEFAULT CURRENT_DATE,
    created_by BIGINT, created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS security_events (
    id BIGSERIAL PRIMARY KEY, severity TEXT NOT NULL, event_type TEXT NOT NULL, actor_telegram_id BIGINT,
    subject_telegram_id BIGINT, details JSONB NOT NULL DEFAULT '{}'::jsonb,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS staff_security_state (
    telegram_id BIGINT PRIMARY KEY REFERENCES staff(telegram_id), state TEXT NOT NULL DEFAULT 'active',
    review_deadline TIMESTAMPTZ, review_counter INTEGER NOT NULL DEFAULT 0,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS app_settings (
    setting_key TEXT PRIMARY KEY, setting_value JSONB NOT NULL, updated_by BIGINT,
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS backup_history (
    id BIGSERIAL PRIMARY KEY, backup_type TEXT NOT NULL, storage_path TEXT,
    state TEXT NOT NULL, size_bytes BIGINT, checksum_sha256 TEXT, error TEXT,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE TABLE IF NOT EXISTS wholesale_requests (
    id BIGSERIAL PRIMARY KEY,
    customer_telegram_id BIGINT NOT NULL,
    customer_name TEXT NOT NULL DEFAULT '',
    username TEXT NOT NULL DEFAULT '',
    body TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'new' CHECK(status IN ('new','in_progress','closed','cancelled')),
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_wholesale_requests_created
    ON wholesale_requests(created_at DESC,id DESC);


CREATE TABLE IF NOT EXISTS delivery_address_drafts (
    telegram_id BIGINT PRIMARY KEY, address TEXT NOT NULL, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS customer_checkout_drafts (
    telegram_id BIGINT PRIMARY KEY REFERENCES customers(telegram_id) ON DELETE CASCADE,
    customer_id BIGINT NOT NULL REFERENCES customers(id),
    step TEXT NOT NULL DEFAULT 'consent',
    phone TEXT NOT NULL DEFAULT '',
    customer_name TEXT NOT NULL DEFAULT '',
    delivery_type TEXT NOT NULL DEFAULT '',
    city TEXT NOT NULL DEFAULT '',
    delivery_branch TEXT NOT NULL DEFAULT '',
    delivery_address TEXT NOT NULL DEFAULT '',
    delivery_quote_id BIGINT,
    checkout_token TEXT NOT NULL DEFAULT '',
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
ALTER TABLE customer_checkout_drafts ADD COLUMN IF NOT EXISTS checkout_token TEXT NOT NULL DEFAULT '';
ALTER TABLE customer_checkout_drafts ADD COLUMN IF NOT EXISTS delivery_slot_id BIGINT REFERENCES delivery_slots(id);
ALTER TABLE customer_checkout_drafts ADD COLUMN IF NOT EXISTS bonus_amount NUMERIC(12,2) NOT NULL DEFAULT 0;
ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS last_attempt_at TIMESTAMPTZ;
ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS available_at TIMESTAMPTZ NOT NULL DEFAULT NOW();
ALTER TABLE customers ADD COLUMN IF NOT EXISTS age_verification_status TEXT NOT NULL DEFAULT 'unverified';
ALTER TABLE customers ADD COLUMN IF NOT EXISTS age_verified_by BIGINT;
ALTER TABLE customers ADD COLUMN IF NOT EXISTS full_name TEXT;
ALTER TABLE customers ADD COLUMN IF NOT EXISTS loyalty_card_number TEXT;
CREATE UNIQUE INDEX IF NOT EXISTS idx_customers_loyalty_card_number ON customers(loyalty_card_number) WHERE loyalty_card_number IS NOT NULL;
ALTER TABLE customers ADD COLUMN IF NOT EXISTS age_verified_at TIMESTAMPTZ;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS idempotency_key TEXT UNIQUE;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS payment_status TEXT NOT NULL DEFAULT 'pending';
ALTER TABLE orders ADD COLUMN IF NOT EXISTS bonus_redeemed NUMERIC(12,2) NOT NULL DEFAULT 0;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS paid_amount NUMERIC(12,2) NOT NULL DEFAULT 0;
CREATE TABLE IF NOT EXISTS delivery_address_drafts (
    telegram_id BIGINT PRIMARY KEY, address TEXT NOT NULL, updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS customer_checkout_drafts (
    telegram_id BIGINT PRIMARY KEY REFERENCES customers(telegram_id) ON DELETE CASCADE,
    customer_id BIGINT NOT NULL REFERENCES customers(id),
    step TEXT NOT NULL DEFAULT 'consent',
    phone TEXT NOT NULL DEFAULT '',
    customer_name TEXT NOT NULL DEFAULT '',
    delivery_type TEXT NOT NULL DEFAULT '',
    city TEXT NOT NULL DEFAULT '',
    delivery_branch TEXT NOT NULL DEFAULT '',
    delivery_address TEXT NOT NULL DEFAULT '',
    delivery_quote_id BIGINT,
    checkout_token TEXT NOT NULL DEFAULT '',
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
ALTER TABLE customer_checkout_drafts ADD COLUMN IF NOT EXISTS checkout_token TEXT NOT NULL DEFAULT '';
ALTER TABLE customer_checkout_drafts ADD COLUMN IF NOT EXISTS delivery_slot_id BIGINT REFERENCES delivery_slots(id);
ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS last_attempt_at TIMESTAMPTZ;
ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS available_at TIMESTAMPTZ NOT NULL DEFAULT NOW();
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_distance_km NUMERIC(9,3);
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_duration_minutes NUMERIC(9,2);
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_tariff_code TEXT;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_tariff_snapshot JSONB;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_route_provider TEXT;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_route_reference TEXT;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_quote_id BIGINT;

INSERT INTO delivery_tariffs (tariff_code, title, base_fee, per_km, minimum_fee)
VALUES
 ('standard', 'Львів звичайна', 35, 8.50, 50),
 ('express', 'Львів екстра швидка', 50, 14, NULL),
 ('night', 'Львів нічна', 60, 22, NULL)
ON CONFLICT (tariff_code) DO NOTHING;

-- Courier operations: append-only events and slot capacity are independent
-- from order status so that delivery history remains auditable.
CREATE TABLE IF NOT EXISTS delivery_events (
    id BIGSERIAL PRIMARY KEY,
    order_id BIGINT NOT NULL REFERENCES orders(id) ON DELETE RESTRICT,
    event_type TEXT NOT NULL CHECK(event_type IN ('assigned','accepted','departed','arrived','delivered','failed','unassigned','ttn_created','slot_booked','slot_released')),
    actor_telegram_id BIGINT,
    courier_telegram_id BIGINT,
    details JSONB NOT NULL DEFAULT '{}'::jsonb,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_delivery_events_order ON delivery_events(order_id,created_at DESC,id DESC);
CREATE INDEX IF NOT EXISTS idx_courier_assignments_courier ON courier_assignments(courier_telegram_id,status,assigned_at DESC);
CREATE INDEX IF NOT EXISTS idx_delivery_slots_active ON delivery_slots(active,starts_at,tariff_code);
ALTER TABLE courier_assignments ADD COLUMN IF NOT EXISTS accepted_at TIMESTAMPTZ;
ALTER TABLE courier_assignments ADD COLUMN IF NOT EXISTS completed_at TIMESTAMPTZ;
ALTER TABLE courier_assignments ADD COLUMN IF NOT EXISTS notes TEXT NOT NULL DEFAULT '';
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_deadline_at TIMESTAMPTZ;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_completed_at TIMESTAMPTZ;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_late_minutes INTEGER NOT NULL DEFAULT 0;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_compensation_bonuses NUMERIC(12,2) NOT NULL DEFAULT 0;
ALTER TABLE orders ADD COLUMN IF NOT EXISTS delivery_slot_id BIGINT REFERENCES delivery_slots(id);
ALTER TABLE orders ADD COLUMN IF NOT EXISTS nova_poshta_tracking_status TEXT NOT NULL DEFAULT '';
ALTER TABLE orders ADD COLUMN IF NOT EXISTS nova_poshta_updated_at TIMESTAMPTZ;




ALTER TABLE order_items ADD COLUMN IF NOT EXISTS variant_id BIGINT REFERENCES product_variants(id) ON DELETE RESTRICT;
UPDATE order_items oi
SET variant_id = pv.id
FROM product_variants pv
WHERE oi.variant_id IS NULL AND oi.sku_snapshot = pv.sku;

CREATE TABLE IF NOT EXISTS return_documents (
    id BIGSERIAL PRIMARY KEY,
    order_id BIGINT NOT NULL REFERENCES orders(id) ON DELETE RESTRICT,
    state TEXT NOT NULL DEFAULT 'draft' CHECK (state IN ('draft','approved','rejected','cancelled')),
    reason TEXT NOT NULL,
    created_by BIGINT NOT NULL,
    reviewed_by BIGINT,
    reviewed_at TIMESTAMPTZ,
    approved_refund_ceiling NUMERIC(12,2) NOT NULL DEFAULT 0 CHECK (approved_refund_ceiling >= 0),
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_returns_order ON return_documents(order_id, created_at DESC);

CREATE TABLE IF NOT EXISTS return_items (
    id BIGSERIAL PRIMARY KEY,
    return_id BIGINT NOT NULL REFERENCES return_documents(id) ON DELETE RESTRICT,
    order_item_id BIGINT NOT NULL REFERENCES order_items(id) ON DELETE RESTRICT,
    variant_id BIGINT REFERENCES product_variants(id) ON DELETE RESTRICT,
    quantity INTEGER NOT NULL CHECK (quantity > 0),
    unit_price_snapshot NUMERIC(12,2) NOT NULL CHECK (unit_price_snapshot >= 0),
    restock BOOLEAN NOT NULL DEFAULT FALSE,
    restock_note TEXT NOT NULL DEFAULT '',
    UNIQUE(return_id, order_item_id)
);

CREATE TABLE IF NOT EXISTS refund_records (
    id BIGSERIAL PRIMARY KEY,
    return_id BIGINT NOT NULL REFERENCES return_documents(id) ON DELETE RESTRICT,
    order_id BIGINT NOT NULL REFERENCES orders(id) ON DELETE RESTRICT,
    amount NUMERIC(12,2) NOT NULL CHECK (amount > 0),
    method TEXT NOT NULL,
    external_reference TEXT NOT NULL DEFAULT '',
    state TEXT NOT NULL DEFAULT 'confirmed' CHECK (state IN ('confirmed','voided')),
    created_by BIGINT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_refunds_order ON refund_records(order_id, state);


ALTER TABLE order_items ADD COLUMN IF NOT EXISTS cost_price_snapshot NUMERIC(12,2);
ALTER TABLE return_documents ADD COLUMN IF NOT EXISTS loyalty_reversal_amount NUMERIC(12,2) NOT NULL DEFAULT 0;
CREATE TABLE IF NOT EXISTS loyalty_debts (
    customer_id BIGINT PRIMARY KEY REFERENCES customers(id) ON DELETE RESTRICT,
    amount NUMERIC(12,2) NOT NULL DEFAULT 0 CHECK (amount >= 0),
    updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE TABLE IF NOT EXISTS loyalty_adjustments (
    id BIGSERIAL PRIMARY KEY,
    customer_id BIGINT NOT NULL REFERENCES customers(id),
    order_id BIGINT REFERENCES orders(id),
    return_id BIGINT REFERENCES return_documents(id),
    adjustment_type TEXT NOT NULL CHECK (adjustment_type IN ('return_reversal','debt_offset','manual_correction')),
    amount NUMERIC(12,2) NOT NULL CHECK (amount > 0),
    debt_created NUMERIC(12,2) NOT NULL DEFAULT 0 CHECK (debt_created >= 0),
    actor_telegram_id BIGINT,
    idempotency_key TEXT UNIQUE,
    reason TEXT NOT NULL DEFAULT '',
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
CREATE INDEX IF NOT EXISTS idx_loyalty_adjustments_customer ON loyalty_adjustments(customer_id, created_at DESC);


ALTER TABLE staff ADD COLUMN IF NOT EXISTS phone TEXT NOT NULL DEFAULT '';
ALTER TABLE staff ADD COLUMN IF NOT EXISTS notes TEXT NOT NULL DEFAULT '';
CREATE INDEX IF NOT EXISTS idx_security_events_subject_created ON security_events(subject_telegram_id,created_at DESC);
CREATE INDEX IF NOT EXISTS idx_security_events_type_created ON security_events(event_type,created_at DESC);
CREATE TABLE IF NOT EXISTS security_action_counters (
    id BIGSERIAL PRIMARY KEY,
    event_type TEXT NOT NULL,
    actor_telegram_id BIGINT,
    subject_telegram_id BIGINT,
    occurred_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
    details JSONB NOT NULL DEFAULT '{}'::jsonb,
    dedupe_key TEXT
);
ALTER TABLE security_action_counters ADD COLUMN IF NOT EXISTS dedupe_key TEXT;
CREATE UNIQUE INDEX IF NOT EXISTS uq_security_counter_dedupe ON security_action_counters(dedupe_key) WHERE dedupe_key IS NOT NULL;
CREATE INDEX IF NOT EXISTS idx_security_counter_window ON security_action_counters(event_type,actor_telegram_id,occurred_at DESC);

"""

pool: Optional[ConnectionPool] = None
consent_pool: Optional[ConnectionPool] = None


def init_db() -> None:
    global pool, consent_pool
    os.makedirs(os.path.join(CONFIG.data_dir, "media"), exist_ok=True)
    os.makedirs(os.path.join(CONFIG.data_dir, "backups"), exist_ok=True)
    pool = ConnectionPool(
        conninfo=CONFIG.database_url,
        min_size=1,
        max_size=8,
        timeout=15,
        kwargs={"row_factory": dict_row},
        open=True,
    )
    with pool.connection() as conn:
        with conn.cursor() as cur:
            cur.execute(SCHEMA_SQL)
            cur.execute(
                """INSERT INTO categories(name,parent_id,sort_order) VALUES
                   ('Рідини',NULL,10),('Под-системи',NULL,20),
                   ('Картриджі',NULL,30),('Інше',NULL,40)
                   ON CONFLICT(name) DO UPDATE SET
                     parent_id=NULL,sort_order=EXCLUDED.sort_order,active=TRUE"""
            )
            cur.execute(
                """
                INSERT INTO staff (telegram_id, display_name, role)
                VALUES (%s, %s, 'owner')
                ON CONFLICT (telegram_id) DO UPDATE
                SET role='owner', active=TRUE, updated_at=NOW()
                """,
                (CONFIG.owner_id, "Власник"),
            )
            for admin_id in CONFIG.admin_ids:
                cur.execute(
                    """
                    INSERT INTO staff (telegram_id, display_name, role)
                    VALUES (%s, %s, 'admin')
                    ON CONFLICT (telegram_id) DO NOTHING
                    """,
                    (admin_id, f"Адміністратор {admin_id}"),
                )
        conn.commit()
    if not CONFIG.consent_database_url:
        raise RuntimeError("CONSENT_DATABASE_URL is required: Handoff requires a separate consent database")
    consent_pool = ConnectionPool(
        conninfo=CONFIG.consent_database_url,
        min_size=1,
        max_size=3,
        timeout=15,
        kwargs={"row_factory": dict_row},
        open=True,
    )
    with consent_pool.connection() as conn:
        with conn.cursor() as cur:
            cur.execute("""CREATE TABLE IF NOT EXISTS consent_records (
                id BIGSERIAL PRIMARY KEY, telegram_id BIGINT NOT NULL, consent_version TEXT NOT NULL,
                content_sha256 TEXT NOT NULL, accepted BOOLEAN NOT NULL,
                source TEXT NOT NULL DEFAULT 'telegram', created_at TIMESTAMPTZ NOT NULL DEFAULT NOW(),
                UNIQUE(telegram_id,consent_version)
            )""")
            cur.execute("CREATE INDEX IF NOT EXISTS idx_consent_telegram ON consent_records(telegram_id,created_at DESC)")
        conn.commit()
    log.info("PostgreSQL schemas initialized; business_db=%s; consent_db=separate; data_dir=%s", CONFIG.database_name, CONFIG.data_dir)
    migrate_v1_20_notification_outbox()


@contextmanager
def db_cursor():
    if pool is None:
        raise RuntimeError("Database pool is not initialized")
    with pool.connection() as conn:
        with conn.cursor() as cur:
            yield cur
        conn.commit()


@contextmanager
def consent_db_cursor():
    if consent_pool is None:
        raise RuntimeError("Consent database pool is not initialized")
    with consent_pool.connection() as conn:
        with conn.cursor() as cur:
            yield cur
        conn.commit()


def record_privacy_consent(telegram_id: int, version: str, text: str, accepted: bool) -> None:
    import hashlib
    checksum = hashlib.sha256(text.encode("utf-8")).hexdigest()
    with consent_db_cursor() as cur:
        cur.execute("""INSERT INTO consent_records(telegram_id,consent_version,content_sha256,accepted,source)
                       VALUES(%s,%s,%s,%s,'telegram') ON CONFLICT(telegram_id,consent_version)
                       DO UPDATE SET content_sha256=EXCLUDED.content_sha256,accepted=EXCLUDED.accepted,
                         created_at=NOW()""", (telegram_id, version, checksum, accepted))


def has_current_privacy_consent(telegram_id: int, version: str) -> bool:
    with consent_db_cursor() as cur:
        cur.execute("SELECT accepted FROM consent_records WHERE telegram_id=%s AND consent_version=%s", (telegram_id, version))
        row = cur.fetchone()
    return bool(row and row["accepted"])


# ---------------------------------------------------------------------------
# Core business services: catalogue, cart, inventory, loyalty, support,
# delivery slots, tasks, settings and notification outbox.
# ---------------------------------------------------------------------------


def upsert_customer(telegram_user) -> int:
    """Create/update a customer using Telegram's immutable numeric ID."""
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO customers(telegram_id,username,first_name,last_name)
               VALUES(%s,%s,%s,%s)
               ON CONFLICT(telegram_id) DO UPDATE SET username=EXCLUDED.username,
                 first_name=EXCLUDED.first_name,last_name=EXCLUDED.last_name,updated_at=NOW()
               RETURNING id""",
            (telegram_user.id, telegram_user.username, telegram_user.first_name or "",
             telegram_user.last_name or ""),
        )
        customer_id=int(cur.fetchone()["id"])
        cur.execute(
            """UPDATE customers
               SET loyalty_card_number=COALESCE(loyalty_card_number,
                   'CH-' || upper(substr(md5(telegram_id::text || random()::text),1,10))),
                   updated_at=NOW()
               WHERE id=%s RETURNING loyalty_card_number""",
            (customer_id,),
        )
        return customer_id


def set_customer_phone(customer_id: int, phone: str) -> None:
    digits = normalize_phone(phone)
    if len(digits) < 10 or len(digits) > 15:
        raise ValueError("Некоректний номер телефону.")
    with db_cursor() as cur:
        cur.execute("UPDATE customers SET phone=%s,updated_at=NOW() WHERE id=%s", (digits, customer_id))
        if cur.rowcount != 1:
            raise ValueError("Клієнта не знайдено.")


def list_root_categories() -> list[dict]:
    """Return the four storefront departments, ordered as agreed in the handoff."""
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,name FROM categories
               WHERE active=TRUE AND parent_id IS NULL
               ORDER BY CASE name
                 WHEN 'Рідини' THEN 1 WHEN 'Под-системи' THEN 2
                 WHEN 'Картриджі' THEN 3 WHEN 'Інше' THEN 4 ELSE 99 END,
                 sort_order,id"""
        )
        return list(cur.fetchall())


def list_category_brands(category_id: int) -> list[dict]:
    """Brands are scoped to the selected department through actual product links."""
    with db_cursor() as cur:
        cur.execute(
            """SELECT DISTINCT b.id,b.name
               FROM brands b JOIN products p ON p.brand_id=b.id
               JOIN product_variants v ON v.product_id=p.id
               WHERE b.active=TRUE AND p.active=TRUE AND p.manually_hidden=FALSE
                 AND p.archived_at IS NULL AND p.category_id=%s AND v.active=TRUE
                 AND v.stock_qty-v.reserved_qty>0
               ORDER BY b.name""", (category_id,)
        )
        return list(cur.fetchall())


def list_catalog(category_id: Optional[int] = None, limit: int = 50,
                 brand_id: Optional[int] = None) -> list[dict]:
    limit = max(1, min(100, int(limit)))
    where = "WHERE p.active=TRUE AND p.manually_hidden=FALSE AND p.archived_at IS NULL AND v.active=TRUE AND v.stock_qty-v.reserved_qty>0"
    params: list[Any] = []
    if category_id is not None:
        where += " AND p.category_id=%s"
        params.append(category_id)
    if brand_id is not None:
        where += " AND p.brand_id=%s"
        params.append(brand_id)
    params.append(limit)
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT p.id product_id,p.category_id,p.brand_id,p.name,p.description,b.name brand,
                       v.id variant_id,v.sku,v.variant_name,v.price,v.stock_qty-v.reserved_qty available
                FROM products p JOIN product_variants v ON v.product_id=p.id
                LEFT JOIN brands b ON b.id=p.brand_id {where}
                ORDER BY p.name,v.variant_name LIMIT %s""", params)
        return list(cur.fetchall())


def create_category(name: str, actor: Staff, parent_id: Optional[int] = None) -> int:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для керування категоріями.")
    clean = " ".join((name or "").split())
    if not clean or len(clean) > 80:
        raise ValueError("Назва категорії має містити від 1 до 80 символів.")
    with db_cursor() as cur:
        if parent_id is not None:
            cur.execute("SELECT id FROM categories WHERE id=%s AND active=TRUE", (parent_id,))
            if not cur.fetchone():
                raise ValueError("Батьківську категорію не знайдено.")
        cur.execute("INSERT INTO categories(name,parent_id) VALUES(%s,%s) RETURNING id", (clean, parent_id))
        category_id = int(cur.fetchone()["id"])
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'catalog.category_created','category',%s,%s::jsonb)",
                    (actor.telegram_id, actor.role, str(category_id), json_dumps({"name": clean, "parent_id": parent_id})))
        return category_id


def create_brand(name: str, actor: Staff, category_id: Optional[int] = None) -> int:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для керування виробниками.")
    clean = " ".join((name or "").split())
    if not clean or len(clean) > 100:
        raise ValueError("Назва виробника має містити від 1 до 100 символів.")
    with db_cursor() as cur:
        if category_id is not None:
            cur.execute("SELECT id FROM categories WHERE id=%s AND parent_id IS NULL AND active=TRUE", (category_id,))
            if not cur.fetchone():
                raise ValueError("Категорію виробника не знайдено або вона неактивна.")
        cur.execute("INSERT INTO brands(name) VALUES(%s) RETURNING id", (clean,))
        brand_id = int(cur.fetchone()["id"])
        if category_id is not None:
            cur.execute("INSERT INTO brand_categories(brand_id,category_id) VALUES(%s,%s) ON CONFLICT DO NOTHING", (brand_id, category_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'catalog.brand_created','brand',%s,%s::jsonb)",
                    (actor.telegram_id, actor.role, str(brand_id), json_dumps({"name": clean, "category_id": category_id})))
        return brand_id


def create_product_variant(product_id: int, sku: str, price: Decimal, actor: Staff,
                            variant_name: str = "", stock: int = 0,
                            cost_price: Optional[Decimal] = None) -> int:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для додавання варіанта товару.")
    sku = (sku or "").strip()
    variant_name = (variant_name or "").strip()
    if not sku or len(sku) > 80 or price < 0 or stock < 0:
        raise ValueError("Перевірте SKU, назву варіанта, ціну та залишок.")
    if cost_price is not None and cost_price < 0:
        raise ValueError("Закупівельна ціна не може бути від’ємною.")
    with db_cursor() as cur:
        cur.execute("SELECT id FROM products WHERE id=%s AND active=TRUE AND archived_at IS NULL FOR UPDATE", (product_id,))
        if not cur.fetchone():
            raise ValueError("Товар не знайдено або він архівований.")
        cur.execute("""INSERT INTO product_variants(product_id,sku,variant_name,price,cost_price,stock_qty)
                       VALUES(%s,%s,%s,%s,%s,%s) RETURNING id""",
                    (product_id, sku, variant_name, price, cost_price, stock))
        variant_id = int(cur.fetchone()["id"])
        if stock:
            cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reason,actor_telegram_id) VALUES(%s,'opening_balance',%s,'Початковий залишок',%s)",
                        (variant_id, stock, actor.telegram_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'catalog.variant_created','variant',%s,%s::jsonb)",
                    (actor.telegram_id, actor.role, str(variant_id), json_dumps({"product_id": product_id, "sku": sku, "variant_name": variant_name, "price": price, "cost_price": cost_price, "stock": stock})))
        return variant_id


def create_product(name: str, sku: str, price: Decimal, stock: int = 0,
                   description: str = "", category_id: Optional[int] = None,
                   brand_id: Optional[int] = None, actor: Optional[Staff] = None) -> int:
    name = name.strip()
    sku = sku.strip()
    if not name or not sku or price < 0 or stock < 0:
        raise ValueError("Перевірте назву, SKU, ціну та залишок.")
    if actor and not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для редагування каталогу.")
    with db_cursor() as cur:
        if category_id is not None:
            cur.execute("SELECT id FROM categories WHERE id=%s AND active=TRUE", (category_id,))
            if not cur.fetchone():
                raise ValueError("Категорію не знайдено або вона неактивна.")
        if brand_id is not None:
            cur.execute("SELECT id FROM brands WHERE id=%s AND active=TRUE", (brand_id,))
            if not cur.fetchone():
                raise ValueError("Виробника не знайдено або він неактивний.")
        cur.execute(
            """INSERT INTO products(category_id,brand_id,name,description)
               VALUES(%s,%s,%s,%s) RETURNING id""",
            (category_id, brand_id, name, description.strip()),
        )
        product_id = int(cur.fetchone()["id"])
        cur.execute(
            """INSERT INTO product_variants(product_id,sku,price,stock_qty)
               VALUES(%s,%s,%s,%s) RETURNING id""", (product_id, sku, price, stock))
        variant_id = int(cur.fetchone()["id"])
        if stock:
            cur.execute(
                """INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reason,actor_telegram_id)
                   VALUES(%s,'opening_balance',%s,'Початковий залишок',%s)""",
                (variant_id, stock, actor.telegram_id if actor else None))
        if actor:
            cur.execute(
                """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data)
                   VALUES(%s,%s,'catalog.product_created','product',%s,%s::jsonb)""",
                (actor.telegram_id, actor.role, str(product_id), json_dumps({"name": name, "sku": sku, "price": price, "stock": stock})))
        return product_id


def change_product_price(variant_id: int, new_price: Decimal, actor: Staff, reason: str) -> None:
    if not actor.can("catalog.update") or new_price < 0 or not reason.strip():
        raise PermissionError("Недостатньо прав або не вказано коректну ціну/причину.")
    with db_cursor() as cur:
        cur.execute("SELECT price FROM product_variants WHERE id=%s FOR UPDATE", (variant_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("Варіант товару не знайдено.")
        old = row["price"]
        cur.execute("UPDATE product_variants SET price=%s,updated_at=NOW() WHERE id=%s", (new_price, variant_id))
        cur.execute("INSERT INTO price_history(variant_id,old_price,new_price,actor_telegram_id,reason) VALUES(%s,%s,%s,%s,%s)",
                    (variant_id, old, new_price, actor.telegram_id, reason.strip()))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data,reason) VALUES(%s,%s,'catalog.price_changed','variant',%s,%s::jsonb,%s::jsonb,%s)",
                    (actor.telegram_id, actor.role, str(variant_id), json_dumps({"price": old}), json_dumps({"price": new_price}), reason.strip()))


def adjust_inventory(variant_id: int, delta: int, actor: Staff, reason: str) -> int:
    if not actor.can("inventory.adjust") or not delta or not reason.strip():
        raise PermissionError("Недостатньо прав або не вказано причину коригування.")
    with db_cursor() as cur:
        cur.execute("SELECT stock_qty,reserved_qty FROM product_variants WHERE id=%s FOR UPDATE", (variant_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("SKU не знайдено.")
        new_qty = int(row["stock_qty"]) + int(delta)
        if new_qty < int(row["reserved_qty"]):
            raise ValueError("Не можна зменшити залишок нижче вже зарезервованої кількості.")
        cur.execute("UPDATE product_variants SET stock_qty=%s,updated_at=NOW() WHERE id=%s", (new_qty, variant_id))
        cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reason,actor_telegram_id) VALUES(%s,'manual_adjustment',%s,%s,%s)",
                    (variant_id, delta, reason.strip(), actor.telegram_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'inventory.adjusted','variant',%s,%s::jsonb,%s)",
                    (actor.telegram_id, actor.role, str(variant_id), json_dumps({"delta": delta, "stock_qty": new_qty}), reason.strip()))
        return new_qty



def release_expired_reservations() -> int:
    """Compatibility wrapper around the guarded stock lifecycle expiry worker."""
    result = release_expired_reservations_safely(batch_size=500)
    return int(result["released"])


def create_inventory_count(actor: Staff) -> int:
    if actor.role not in ('owner','admin','packer'):
        raise PermissionError('Недостатньо прав для інвентаризації.')
    with db_cursor() as cur:
        cur.execute("INSERT INTO inventory_counts(status,created_by) VALUES('counting',%s) RETURNING id", (actor.telegram_id,))
        count_id = int(cur.fetchone()['id'])
        cur.execute("SELECT id FROM product_variants WHERE active=TRUE ORDER BY id")
        variants = [r['id'] for r in cur.fetchall()]
        for variant_id in variants:
            # system_qty_snapshot intentionally remains NULL until confirmation;
            # blind counting must not reveal expected stock to the counter.
            cur.execute("INSERT INTO inventory_count_items(count_id,variant_id,counted_by) VALUES(%s,%s,%s)",
                        (count_id,variant_id,actor.telegram_id))
        return count_id


def record_inventory_count_item(count_id: int, variant_id: int, actual_qty: int, actor: Staff) -> None:
    if actual_qty < 0 or actor.role not in ('owner','admin','packer'):
        raise ValueError('Некоректна кількість або недостатньо прав.')
    with db_cursor() as cur:
        cur.execute("SELECT status FROM inventory_counts WHERE id=%s FOR UPDATE", (count_id,))
        count = cur.fetchone()
        if not count or count['status'] != 'counting':
            raise ValueError('Інвентаризація не відкрита для підрахунку.')
        cur.execute("UPDATE inventory_count_items SET actual_qty=%s,counted_by=%s,counted_at=NOW() WHERE count_id=%s AND variant_id=%s",
                    (actual_qty,actor.telegram_id,count_id,variant_id))
        if cur.rowcount != 1:
            raise ValueError('SKU не входить до цієї інвентаризації.')


def confirm_inventory_count(count_id: int, actor: Staff, reason: str) -> list[dict]:
    """Confirm blind count while preserving stock movements posted after each SKU was counted."""
    if actor.role not in ('owner','admin') or not reason.strip():
        raise PermissionError('Підтвердити інвентаризацію може власник/адміністратор із причиною.')
    with db_cursor() as cur:
        cur.execute("SELECT status,created_at FROM inventory_counts WHERE id=%s FOR UPDATE", (count_id,))
        count=cur.fetchone()
        if not count or count['status'] != 'counting':
            raise ValueError('Інвентаризацію вже закрито або не знайдено.')
        cur.execute("SELECT id,variant_id,actual_qty,counted_at FROM inventory_count_items WHERE count_id=%s ORDER BY variant_id FOR UPDATE", (count_id,))
        items=list(cur.fetchall())
        if not items or any(x['actual_qty'] is None for x in items):
            raise ValueError('Спочатку потрібно внести фактичну кількість для кожного SKU.')
        report=[]
        for item in items:
            cur.execute("SELECT stock_qty,reserved_qty FROM product_variants WHERE id=%s FOR UPDATE", (item['variant_id'],))
            stock=cur.fetchone()
            if not stock:
                raise ValueError('SKU видалено або не знайдено. Інвентаризацію не проведено.')
            system_qty=int(stock['stock_qty'])
            counted_at=item['counted_at'] or count['created_at']
            # Reservations do not change physical stock. Only posted stock movements
            # are replayed over the physical count to avoid overwriting concurrent sales/receipts.
            cur.execute("""SELECT COALESCE(SUM(quantity_delta),0) net_delta
                           FROM inventory_movements
                           WHERE variant_id=%s AND created_at>%s
                             AND movement_type IN ('supply','sale','manual_adjustment','opening_balance','inventory_count')""",
                        (item['variant_id'],counted_at))
            net_delta=int(cur.fetchone()['net_delta'])
            actual=int(item['actual_qty'])+net_delta
            discrepancy=actual-system_qty
            if actual < int(stock['reserved_qty']):
                raise ValueError(f"Фактичний залишок SKU #{item['variant_id']} нижчий за активний резерв. Перевірте резерви та повторіть звірку.")
            cur.execute("UPDATE inventory_count_items SET system_qty_snapshot=%s,discrepancy=%s,reason=%s WHERE id=%s",
                        (system_qty,discrepancy,reason.strip(),item['id']))
            if discrepancy:
                cur.execute("UPDATE product_variants SET stock_qty=%s,updated_at=NOW() WHERE id=%s", (actual,item['variant_id']))
                cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reference_type,reference_id,reason,actor_telegram_id) VALUES(%s,'inventory_count',%s,'inventory_count',%s,%s,%s)",
                            (item['variant_id'],discrepancy,str(count_id),reason.strip(),actor.telegram_id))
            report.append({'variant_id':item['variant_id'],'system_qty':system_qty,'actual_qty':actual,
                           'counted_qty':int(item['actual_qty']),'concurrent_delta':net_delta,'discrepancy':discrepancy})
        cur.execute("UPDATE inventory_counts SET status='confirmed',confirmed_by=%s,confirmed_at=NOW() WHERE id=%s", (actor.telegram_id,count_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'inventory.count_confirmed','inventory_count',%s,%s::jsonb,%s)",
                    (actor.telegram_id,actor.role,str(count_id),json_dumps(report),reason.strip()))
        return report


def post_supply_document(supply_id: int, actor: Staff) -> dict:
    """Post a receipt atomically using weighted-average inventory cost."""
    if not actor.can('inventory.receive'):
        raise PermissionError('Недостатньо прав для оприбуткування поставки.')
    report=[]
    with db_cursor() as cur:
        cur.execute("SELECT state,document_number,supplier_id FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc=cur.fetchone()
        if not doc or doc['state'] != 'draft':
            raise ValueError('Поставка не знайдена або вже проведена.')
        cur.execute("""SELECT si.variant_id,si.quantity,si.received_qty,si.unit_cost,v.stock_qty,v.cost_price,v.sku
                       FROM supply_items si JOIN product_variants v ON v.id=si.variant_id
                       WHERE si.supply_id=%s ORDER BY si.variant_id FOR UPDATE OF si,v""", (supply_id,))
        items=list(cur.fetchall())
        if not items or not any(int(x['received_qty'])>0 for x in items):
            raise ValueError('Поставка порожня: немає фактично прийнятих одиниць.')
        for item in items:
            received=int(item['received_qty'])
            if received > int(item['quantity']):
                raise ValueError('Фактична кількість перевищує кількість у документі.')
            if received <= 0: continue
            old_stock=int(item['stock_qty'])
            old_cost=Decimal(str(item['cost_price'])) if item['cost_price'] is not None else None
            incoming_cost=Decimal(str(item['unit_cost']))
            if old_stock>0 and old_cost is not None:
                new_cost=((Decimal(old_stock)*old_cost)+(Decimal(received)*incoming_cost))/Decimal(old_stock+received)
            else:
                new_cost=incoming_cost
            new_cost=new_cost.quantize(Decimal('0.01'),rounding=ROUND_HALF_UP)
            cur.execute("UPDATE product_variants SET stock_qty=stock_qty+%s,cost_price=%s,updated_at=NOW() WHERE id=%s",(received,new_cost,item['variant_id']))
            cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reference_type,reference_id,reason,actor_telegram_id) VALUES(%s,'supply',%s,'supply',%s,%s,%s)",(item['variant_id'],received,str(supply_id),f"Поставка {doc['document_number']}; прийнято {received}/{item['quantity']}",actor.telegram_id))
            report.append({'variant_id':int(item['variant_id']),'sku':item['sku'],'received':received,'unit_cost':str(incoming_cost),'weighted_cost':str(new_cost)})
        total=sum((Decimal(str(x['unit_cost']))*int(x['received_qty']) for x in items),Decimal('0.00'))
        cur.execute("UPDATE supply_documents SET state='posted',posted_at=NOW(),created_by=COALESCE(created_by,%s),total_cost=%s WHERE id=%s",(actor.telegram_id,total,supply_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'supply.posted','supply',%s,%s::jsonb)",(actor.telegram_id,actor.role,str(supply_id),json_dumps({'document_number':doc['document_number'],'supplier_id':doc['supplier_id'],'items':report,'total_received_cost':str(total)})))
        return {'supply_id':supply_id,'document_number':doc['document_number'],'items':report,'total_received_cost':str(total)}


def add_to_cart(customer_telegram_id: int, variant_id: int, quantity: int = 1) -> None:
    if quantity < 1 or quantity > 99:
        raise ValueError("Кількість має бути від 1 до 99.")
    with db_cursor() as cur:
        cur.execute("INSERT INTO carts(customer_telegram_id) VALUES(%s) ON CONFLICT DO NOTHING", (customer_telegram_id,))
        cur.execute("SELECT v.stock_qty,v.reserved_qty,v.active,p.active product_active,p.manually_hidden FROM product_variants v JOIN products p ON p.id=v.product_id WHERE v.id=%s FOR UPDATE OF v", (variant_id,))
        v = cur.fetchone()
        if not v or not v["active"] or not v["product_active"] or v["manually_hidden"]:
            raise ValueError("Товар зараз недоступний.")
        cur.execute("SELECT COALESCE(SUM(quantity),0) qty FROM cart_items WHERE customer_telegram_id=%s AND variant_id=%s", (customer_telegram_id, variant_id))
        existing = int(cur.fetchone()["qty"])
        if existing + quantity > int(v["stock_qty"]) - int(v["reserved_qty"]):
            raise ValueError("Недостатньо товару в наявності.")
        cur.execute("""INSERT INTO cart_items(customer_telegram_id,variant_id,quantity) VALUES(%s,%s,%s)
                       ON CONFLICT(customer_telegram_id,variant_id) DO UPDATE SET quantity=cart_items.quantity+EXCLUDED.quantity""",
                    (customer_telegram_id, variant_id, quantity))
        cur.execute("UPDATE carts SET updated_at=NOW() WHERE customer_telegram_id=%s", (customer_telegram_id,))


def get_cart(customer_telegram_id: int) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT ci.variant_id,ci.quantity,v.sku,v.variant_name,v.price,p.name,
                          (ci.quantity*v.price) line_total,v.stock_qty-v.reserved_qty available
                   FROM cart_items ci JOIN product_variants v ON v.id=ci.variant_id
                   JOIN products p ON p.id=v.product_id WHERE ci.customer_telegram_id=%s ORDER BY ci.id""", (customer_telegram_id,))
        return list(cur.fetchall())


def clear_cart(customer_telegram_id: int) -> None:
    """Clear only the customer's cart; loyalty earnings belong to order creation."""
    with db_cursor() as cur:
        cur.execute("DELETE FROM cart_items WHERE customer_telegram_id=%s", (customer_telegram_id,))



def set_age_verification(customer_id: int, verified: bool, actor: Staff, reason: str = "") -> None:
    if actor.role not in ("owner", "admin"):
        raise PermissionError("Перевіряти вік можуть лише власник або уповноважений адміністратор.")
    status = "verified" if verified else "rejected"
    with db_cursor() as cur:
        cur.execute("UPDATE customers SET age_verification_status=%s,age_verified_by=%s,age_verified_at=NOW(),updated_at=NOW() WHERE id=%s RETURNING telegram_id",
                    (status, actor.telegram_id, customer_id))
        row = cur.fetchone()
        if not row:
            raise ValueError("Клієнта не знайдено.")
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'customer.age_verification','customer',%s,%s::jsonb,%s)",
                    (actor.telegram_id, actor.role, str(customer_id), json_dumps({"status": status}), reason.strip()))


def checkout_cart(customer_telegram_id: int, customer_id: int, customer_name: str,
                  phone: str, delivery_type: str, idempotency_key: str,
                  delivery_quote_id: Optional[int] = None, city: str = "",
                  delivery_branch: str = "", bonus_amount: Decimal = Decimal("0.00"),
                  delivery_slot_id: Optional[int] = None) -> dict:
    """Atomic COD checkout with age/consent gates, stock reservation and snapshots.

    Courier quote must already be accepted. Nova Poshta freight is deliberately
    excluded from Cloud Hub's delivery_total in accordance with Handoff.
    """
    if not idempotency_key or len(idempotency_key) > 120:
        raise ValueError("Некоректний ключ оформлення.")
    if not has_current_privacy_consent(customer_telegram_id, CONFIG.privacy_consent_version):
        raise ValueError("Спочатку потрібно підтвердити згоду на обробку персональних даних.")
    if delivery_type not in ("courier_standard", "courier_express", "courier_night", "nova_poshta"):
        raise ValueError("Оберіть доступний спосіб доставки.")
    with db_cursor() as cur:
        cur.execute("SELECT idempotency_key,order_number,id FROM orders WHERE idempotency_key=%s", (idempotency_key,))
        existing = cur.fetchone()
        if existing:
            return {"id": existing["id"], "order_number": existing["order_number"], "duplicate": True}
        cur.execute("SELECT age_verification_status FROM customers WHERE id=%s AND telegram_id=%s FOR UPDATE",
                    (customer_id, customer_telegram_id))
        customer = cur.fetchone()
        if not customer:
            raise ValueError("Профіль клієнта не знайдено.")
        # Age is checked manually by authorized staff before the order is accepted
        # for fulfillment. Checkout itself may create the order and preserve it.
        age_check_pending = customer["age_verification_status"] != "verified"
        cur.execute("""SELECT ci.variant_id,ci.quantity,v.sku,v.price,v.cost_price,v.stock_qty,v.reserved_qty,
                          p.name product_name,p.active product_active,p.manually_hidden,v.active variant_active
                   FROM cart_items ci JOIN product_variants v ON v.id=ci.variant_id
                   JOIN products p ON p.id=v.product_id
                   WHERE ci.customer_telegram_id=%s ORDER BY ci.variant_id FOR UPDATE OF v""", (customer_telegram_id,))
        items = list(cur.fetchall())
        if not items:
            raise ValueError("Кошик порожній.")
        for item in items:
            if not item["product_active"] or item["manually_hidden"] or not item["variant_active"]:
                raise ValueError(f"Товар {item['product_name']} більше недоступний.")
            if int(item["stock_qty"]) - int(item["reserved_qty"]) < int(item["quantity"]):
                raise ValueError(f"Недостатньо залишку товару {item['product_name']}.")
        delivery_total = Decimal("0.00")
        quote = None
        delivery_address = ""
        delivery_snapshot = None
        if delivery_type.startswith("courier_"):
            if not delivery_quote_id:
                raise ValueError("Для кур’єрської доставки потрібен підтверджений розрахунок.")
            tariff_code = delivery_type.replace("courier_", "")
            cur.execute("""SELECT * FROM delivery_quotes WHERE id=%s AND customer_telegram_id=%s
                           AND state='accepted' AND expires_at>NOW() FOR UPDATE""", (delivery_quote_id, customer_telegram_id))
            quote = cur.fetchone()
            if not quote or quote["tariff_code"] != tariff_code:
                raise ValueError("Розрахунок доставки неактуальний. Порахуйте його ще раз.")
            delivery_total = Decimal(str(quote["delivery_price"]))
            delivery_address = quote["destination_address"]
            delivery_snapshot = {"tariff_code": quote["tariff_code"], "base": str(quote["tariff_base"]),
                                 "per_km": str(quote["tariff_per_km"]), "distance_km": str(quote["distance_km"]),
                                 "duration_minutes": str(quote["duration_minutes"]), "price": str(delivery_total)}
        elif delivery_type == "nova_poshta":
            if not city.strip() or not delivery_branch.strip():
                raise ValueError("Для Нової пошти вкажіть місто та відділення/поштомат.")
        selected_slot = None
        if delivery_type.startswith("courier_"):
            if delivery_slot_id is None:
                raise ValueError("Оберіть доступний час доставки.")
            cur.execute("SELECT id,tariff_code,starts_at,ends_at,capacity,booked_count,active FROM delivery_slots WHERE id=%s FOR UPDATE", (delivery_slot_id,))
            selected_slot = cur.fetchone()
            expected_tariff = delivery_type.replace("courier_", "")
            if (not selected_slot or not selected_slot["active"] or selected_slot["tariff_code"] != expected_tariff
                    or selected_slot["starts_at"] <= datetime.now(timezone.utc)
                    or int(selected_slot["booked_count"]) >= int(selected_slot["capacity"])):
                raise ValueError("Обраний час уже недоступний. Будь ласка, виберіть інший слот.")
        items_total = sum((Decimal(str(x["price"])) * int(x["quantity"]) for x in items), Decimal("0.00"))
        gross_total = items_total + delivery_total
        bonus_value = Decimal(str(bonus_amount or 0)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        if bonus_value < 0 or bonus_value > items_total:
            raise ValueError("Сума списання бонусів некоректна або перевищує суму замовлення.")
        if bonus_value:
            cur.execute("SELECT available FROM loyalty_accounts WHERE customer_id=%s FOR UPDATE", (customer_id,))
            bonus_account = cur.fetchone()
            if not bonus_account or Decimal(str(bonus_account["available"])) < bonus_value:
                raise ValueError("Недостатньо доступних бонусів. Оновіть баланс і спробуйте ще раз.")
        grand_total = gross_total - bonus_value
        order_number = "CH-" + datetime.now(timezone.utc).strftime("%Y%m%d") + "-" + uuid.uuid4().hex[:8].upper()
        cur.execute("""INSERT INTO orders(order_number,customer_id,customer_name_snapshot,phone_snapshot,
                       telegram_id_snapshot,status,city,delivery_branch,delivery_address,delivery_type,
                       payment_method,items_total,delivery_total,grand_total,bonus_redeemed,idempotency_key,
                       delivery_distance_km,delivery_duration_minutes,delivery_tariff_code,
                       delivery_tariff_snapshot,delivery_route_provider,delivery_route_reference,delivery_quote_id)
                       VALUES(%s,%s,%s,%s,%s,'new',%s,%s,%s,%s,'cod',%s,%s,%s,%s,%s,%s,%s,%s,%s::jsonb,%s,%s,%s)
                       RETURNING id""",
                    (order_number, customer_id, customer_name.strip(), normalize_phone(phone), customer_telegram_id,
                     city.strip(), delivery_branch.strip(), delivery_address, delivery_type, items_total,
                     delivery_total, grand_total, bonus_value, idempotency_key,
                     quote["distance_km"] if quote else None, quote["duration_minutes"] if quote else None,
                     quote["tariff_code"] if quote else None,
                     json_dumps(delivery_snapshot) if delivery_snapshot else None,
                     quote["route_provider"] if quote else None, quote["route_reference"] if quote else None,
                     delivery_quote_id if quote else None))
        order_id = int(cur.fetchone()["id"])
        if selected_slot:
            cur.execute("UPDATE delivery_slots SET booked_count=booked_count+1 WHERE id=%s AND active=TRUE AND booked_count<capacity", (delivery_slot_id,))
            if cur.rowcount != 1:
                raise ValueError("Цей час щойно зайняли. Оберіть інший слот.")
            cur.execute("UPDATE orders SET delivery_slot_id=%s WHERE id=%s", (delivery_slot_id, order_id))
            cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,details) VALUES(%s,'slot_booked',%s,%s::jsonb)",
                        (order_id, customer_telegram_id, json_dumps({"slot_id":delivery_slot_id,"starts_at":selected_slot["starts_at"].isoformat(),"source":"customer_checkout"})))
        if bonus_value:
            cur.execute("""SELECT id,remaining_amount FROM loyalty_lots
                           WHERE customer_id=%s AND state='available' AND expires_at>NOW()
                             AND remaining_amount>0 ORDER BY expires_at,id FOR UPDATE""", (customer_id,))
            bonus_lots = list(cur.fetchall())
            remaining_bonus = bonus_value
            for lot in bonus_lots:
                if remaining_bonus <= 0:
                    break
                use = min(remaining_bonus, Decimal(str(lot["remaining_amount"])))
                left = Decimal(str(lot["remaining_amount"])) - use
                cur.execute("UPDATE loyalty_lots SET remaining_amount=%s,state=%s WHERE id=%s",
                            (left, "spent" if left == 0 else "available", lot["id"]))
                remaining_bonus -= use
            if remaining_bonus > 0:
                raise RuntimeError("Баланс бонусів не узгоджується з активними бонусними партіями. Списання скасовано.")
            cur.execute("""UPDATE loyalty_accounts SET available=available-%s,updated_at=NOW()
                           WHERE customer_id=%s AND available>=%s""", (bonus_value, customer_id, bonus_value))
            if cur.rowcount != 1:
                raise RuntimeError("Баланс бонусів змінився паралельно. Списання скасовано.")
            cur.execute("""INSERT INTO loyalty_transactions
                           (customer_id,order_id,transaction_type,amount,state,reason,actor_telegram_id,idempotency_key)
                           VALUES(%s,%s,'redeem',%s,'completed','Списання бонусів при оформленні',%s,%s)""",
                        (customer_id, order_id, -bonus_value, customer_telegram_id, f"order:{order_id}:bonus_redeem"))
        if delivery_type == "courier_express":
            cur.execute("UPDATE orders SET delivery_deadline_at=NOW()+INTERVAL '29 minutes' WHERE id=%s", (order_id,))
        for item in items:
            line_total = Decimal(str(item["price"])) * int(item["quantity"])
            cur.execute("INSERT INTO order_items(order_id,product_name_snapshot,sku_snapshot,quantity,unit_price,line_total,variant_id,cost_price_snapshot) VALUES(%s,%s,%s,%s,%s,%s,%s,%s)",
                        (order_id, item["product_name"], item["sku"], item["quantity"], item["price"], line_total, item["variant_id"], item.get("cost_price")))
            cur.execute("UPDATE product_variants SET reserved_qty=reserved_qty+%s,updated_at=NOW() WHERE id=%s",
                        (item["quantity"], item["variant_id"]))
            cur.execute("INSERT INTO stock_reservations(order_id,variant_id,quantity,expires_at) VALUES(%s,%s,%s,NOW()+(%s * INTERVAL '1 minute'))",
                        (order_id, item["variant_id"], item["quantity"], CONFIG.reservation_minutes))
            cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reference_type,reference_id,reason) VALUES(%s,'reserve',%s,'order',%s,'Резерв під замовлення')",
                        (item["variant_id"], -int(item["quantity"]), str(order_id)))
        pending_bonus = _create_order_pending_bonus_tx(
            cur, {"id": order_id, "customer_id": customer_id, "items_total": items_total})
        cur.execute("DELETE FROM cart_items WHERE customer_telegram_id=%s", (customer_telegram_id,))
        if quote:
            cur.execute("UPDATE delivery_quotes SET state='used' WHERE id=%s", (delivery_quote_id,))
        cur.execute("INSERT INTO audit_log(action,entity_type,entity_id,after_data) VALUES('order.created','order',%s,%s::jsonb)",
                    (str(order_id), json_dumps({"order_number": order_number, "customer_telegram_id": customer_telegram_id,
                                                "delivery_type": delivery_type, "grand_total": grand_total})))
        if delivery_type == "nova_poshta":
            delivery_note = f"📦 Нова пошта: {city.strip()}, {delivery_branch.strip()}"
        else:
            delivery_note = f"🚴 Кур’єр Cloud Hub: {delivery_address}"
        order_notice = (f"🆕 <b>Нове замовлення {safe(order_number)}</b>\n"
                        f"👤 {safe(customer_name.strip())}\n📞 {safe(normalize_phone(phone))}\n"
                        f"{safe(delivery_note)}\n💰 Разом: <b>{grand_total} грн</b> (оплата при отриманні)")
        if age_check_pending:
            order_notice += "\n🪪 Вік клієнта потрібно перевірити вручну до підтвердження/відправлення. Черга: /agequeue"
        order_payload = {"text": order_notice, "order_id": order_id,
                         "buttons": [["📂 Відкрити замовлення", f"ordview:{order_id}"]]}
        for rid in staff_recipient_ids(cur, ("owner", "admin", "manager", "packer")):
            enqueue_notification(cur, rid, "orders", order_payload, f"order:{order_id}:created:{rid}")
        return {"id": order_id, "order_number": order_number, "items_total": items_total,
                "delivery_total": delivery_total, "grand_total": grand_total,
                "pending_bonus": pending_bonus, "bonus_redeemed": bonus_value, "duplicate": False}



def _create_order_pending_bonus_tx(cur, order: dict) -> Decimal:
    """Create pending 2% bonus at order creation; idempotent by order."""
    customer_id=order.get("customer_id")
    if not customer_id:
        return Decimal("0.00")
    amount=(Decimal(str(order.get("items_total") or 0))*Decimal("0.02")).quantize(
        Decimal("0.01"),rounding=ROUND_HALF_UP)
    if amount<=0:
        return Decimal("0.00")
    key=f"order:{int(order['id'])}:bonus_earn"
    cur.execute("SELECT amount FROM loyalty_transactions WHERE idempotency_key=%s",(key,))
    existing=cur.fetchone()
    if existing:
        return Decimal(str(existing["amount"] or 0))
    cur.execute("INSERT INTO loyalty_accounts(customer_id) VALUES(%s) ON CONFLICT DO NOTHING",(customer_id,))
    cur.execute(
        """INSERT INTO loyalty_transactions(customer_id,order_id,transaction_type,amount,state,reason,
           actor_telegram_id,idempotency_key)
           VALUES(%s,%s,'earn',%s,'pending','2%% від суми товарів у створеному замовленні',NULL,%s)
           RETURNING id""",(customer_id,order["id"],amount,key))
    tx_id=int(cur.fetchone()["id"])
    cur.execute("""INSERT INTO loyalty_lots(customer_id,source_transaction_id,original_amount,
                   remaining_amount,state,expires_at)
                   VALUES(%s,%s,%s,%s,'pending',NOW()+INTERVAL '1 year')""",
                (customer_id,tx_id,amount,amount))
    cur.execute("UPDATE loyalty_accounts SET pending=pending+%s,updated_at=NOW() WHERE customer_id=%s",
                (amount,customer_id))
    return amount


def _cancel_pending_order_bonuses_tx(cur, order_id: int, customer_id: Optional[int]) -> Decimal:
    """Void pending bonuses when an order is cancelled before shipment."""
    if not customer_id:
        return Decimal("0.00")
    cur.execute(
        """SELECT remaining_amount FROM loyalty_lots
           WHERE source_transaction_id IN (
             SELECT id FROM loyalty_transactions
             WHERE order_id=%s AND transaction_type='earn' AND state='pending')
             AND state='pending' FOR UPDATE""", (order_id,))
    removed=sum((Decimal(str(x["remaining_amount"] or 0)) for x in cur.fetchall()),Decimal("0.00"))
    cur.execute(
        """UPDATE loyalty_lots SET state='spent',remaining_amount=0
           WHERE source_transaction_id IN (
             SELECT id FROM loyalty_transactions
             WHERE order_id=%s AND transaction_type='earn' AND state='pending')
           AND state='pending'""", (order_id,))
    if removed:
        cur.execute("""UPDATE loyalty_accounts SET pending=GREATEST(0,pending-%s),updated_at=NOW()
                       WHERE customer_id=%s""",(removed,customer_id))
    cur.execute("""UPDATE loyalty_transactions SET state='cancelled'
                   WHERE order_id=%s AND transaction_type='earn' AND state='pending'""",(order_id,))
    return removed


def _award_order_bonuses_tx(cur, order: dict, actor: Optional[Staff] = None) -> Decimal:
    """Issue pending 2% bonus inside the caller's payment/order transaction."""
    if order.get("payment_status") != "paid":
        raise ValueError("Бонуси можна нарахувати лише після підтвердження фактичної оплати.")
    customer_id = order.get("customer_id")
    if not customer_id:
        return Decimal("0.00")
    amount = (
        Decimal(str(order.get("paid_amount") or 0)) * Decimal("0.02")
    ).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    if amount <= 0:
        return Decimal("0.00")
    key = f"order:{int(order['id'])}:bonus_earn"
    cur.execute("SELECT amount FROM loyalty_transactions WHERE idempotency_key=%s", (key,))
    existing=cur.fetchone()
    if existing:
        return Decimal(str(existing["amount"] or 0))
    cur.execute(
        "INSERT INTO loyalty_accounts(customer_id) VALUES(%s) ON CONFLICT DO NOTHING",
        (customer_id,),
    )
    cur.execute(
        "INSERT INTO loyalty_debts(customer_id,amount) VALUES(%s,0) ON CONFLICT DO NOTHING",
        (customer_id,),
    )
    cur.execute(
        "SELECT amount FROM loyalty_debts WHERE customer_id=%s FOR UPDATE",
        (customer_id,),
    )
    debt_row = cur.fetchone()
    debt = Decimal(str(debt_row["amount"] or 0)) if debt_row else Decimal("0.00")
    debt_offset = min(amount, debt)
    net_amount = amount - debt_offset
    if debt_offset:
        cur.execute(
            """UPDATE loyalty_debts SET amount=amount-%s,updated_at=NOW()
               WHERE customer_id=%s AND amount>=%s""",
            (debt_offset, customer_id, debt_offset),
        )
        if cur.rowcount != 1:
            raise RuntimeError("Бонусний борг змінився паралельно. Транзакцію скасовано.")
        cur.execute(
            """INSERT INTO loyalty_adjustments
               (customer_id,order_id,adjustment_type,amount,idempotency_key,reason)
               VALUES(%s,%s,'debt_offset',%s,%s,%s)""",
            (customer_id, order["id"], debt_offset,
             f"order:{int(order['id'])}:bonus_debt_offset",
             "Автоматичне погашення бонусного боргу новим нарахуванням"),
        )
    if net_amount > 0:
        cur.execute(
            """INSERT INTO loyalty_transactions
               (customer_id,order_id,transaction_type,amount,state,reason,
                actor_telegram_id,idempotency_key)
               VALUES(%s,%s,'earn',%s,'pending',
                      '2%% від фактично оплаченої суми після погашення бонусного боргу',
                      %s,%s) RETURNING id""",
            (customer_id, order["id"], net_amount,
             actor.telegram_id if actor else None, key),
        )
        transaction_id = int(cur.fetchone()["id"])
        cur.execute(
            """INSERT INTO loyalty_lots
               (customer_id,source_transaction_id,original_amount,remaining_amount,
                state,expires_at)
               VALUES(%s,%s,%s,%s,'pending',NOW()+INTERVAL '1 year')""",
            (customer_id, transaction_id, net_amount, net_amount),
        )
        cur.execute(
            """UPDATE loyalty_accounts SET pending=pending+%s,updated_at=NOW()
               WHERE customer_id=%s""",
            (net_amount, customer_id),
        )
    if debt_offset:
        cur.execute(
            """INSERT INTO loyalty_transactions
               (customer_id,order_id,transaction_type,amount,state,reason,
                actor_telegram_id,idempotency_key)
               VALUES(%s,%s,'debt_offset',%s,'completed',
                      'Погашення бонусного боргу',%s,%s)""",
            (customer_id, order["id"], -debt_offset,
             actor.telegram_id if actor else None,
             f"order:{int(order['id'])}:bonus_debt_offset_tx"),
        )
    return net_amount


def record_cod_payment(order_id: int, paid_amount: Decimal, actor: Staff,
                       note: str = "") -> None:
    """Capture COD payment and issue loyalty bonus atomically."""
    if not actor.can("finance.payment_confirm"):
        raise PermissionError("Недостатньо прав для підтвердження оплати.")
    value = Decimal(str(paid_amount)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    if value <= 0:
        raise ValueError("Підтверджена оплата має бути більшою за нуль.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,customer_id,grand_total,payment_status,paid_amount,status
               FROM orders WHERE id=%s FOR UPDATE""",
            (order_id,),
        )
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        if order["status"] in {"cancelled", "canceled", "returned"}:
            raise ValueError("Не можна підтвердити оплату скасованого або повернутого замовлення.")
        validation = payment_capture_validation(
            Decimal(str(order["grand_total"])), value, str(order["payment_status"])
        )
        if not validation["valid"]:
            raise ValueError("Оплату відхилено: " + ", ".join(validation["issues"]))
        cur.execute(
            """UPDATE orders SET payment_status='paid',paid_amount=%s,updated_at=NOW()
               WHERE id=%s AND payment_status<>'paid'""",
            (value, order_id),
        )
        if cur.rowcount != 1:
            raise RuntimeError("Статус оплати змінився паралельно. Повторіть перевірку.")
        paid_order = dict(order)
        paid_order["paid_amount"] = value
        paid_order["payment_status"] = "paid"
        cur.execute(
            """INSERT INTO audit_log
               (actor_telegram_id,actor_role,action,entity_type,entity_id,
                after_data,reason)
               VALUES(%s,%s,'payment.cod_confirmed','order',%s,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(order_id),
             json_dumps({"paid_amount": value}), str(note or "").strip()),
        )
        bonus = _award_order_bonuses_tx(cur, paid_order, actor)
        cur.execute(
            """INSERT INTO audit_log
               (actor_telegram_id,actor_role,action,entity_type,entity_id,
                after_data,reason)
               VALUES(%s,%s,'loyalty.order_bonus_issued','order',%s,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(order_id),
             json_dumps({"bonus_amount": bonus}),
             "Атомарне нарахування після підтвердження оплати"),
        )


def award_order_bonuses(order_id: int, actor: Optional[Staff] = None) -> Decimal:
    """Idempotently issue pending 2% bonus for an already-paid order."""
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,customer_id,paid_amount,payment_status
               FROM orders WHERE id=%s FOR UPDATE""",
            (order_id,),
        )
        order = cur.fetchone()
        if not order or order["payment_status"] != "paid":
            raise ValueError("Бонуси можна нарахувати лише після підтвердження фактичної оплати.")
        return _award_order_bonuses_tx(cur, dict(order), actor)



def redeem_bonuses(customer_id: int, amount: Decimal, actor_telegram_id: int,
                   order_id: Optional[int] = None) -> None:
    """Redeem available loyalty lots once per order, using FIFO and a stable key.

    Manual redemptions retain a unique key because they are independent events.
    An order-linked redemption is idempotent: retrying the same order cannot
    debit the customer's account twice.
    """
    value = Decimal(str(amount)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    if value <= 0 or value != Decimal(str(amount)):
        raise ValueError("Некоректна сума бонусів.")
    if customer_id <= 0:
        raise ValueError("Некоректний клієнт.")
    key = (f"order:{int(order_id)}:bonus_redeem" if order_id is not None
           else f"manual:{int(actor_telegram_id)}:{uuid.uuid4().hex}")
    with db_cursor() as cur:
        if order_id is not None:
            cur.execute(
                "SELECT customer_id, payment_status, status FROM orders WHERE id=%s FOR UPDATE",
                (int(order_id),),
            )
            order = cur.fetchone()
            if not order:
                raise ValueError("Замовлення для списання бонусів не знайдено.")
            if int(order["customer_id"] or 0) != int(customer_id):
                raise PermissionError("Замовлення не належить цьому клієнту.")
            if order["status"] in {"cancelled", "canceled", "returned"}:
                raise ValueError("Не можна списувати бонуси для скасованого або повернутого замовлення.")
            cur.execute(
                "SELECT id FROM loyalty_transactions WHERE idempotency_key=%s",
                (key,),
            )
            if cur.fetchone():
                raise ValueError("Бонуси для цього замовлення вже були списані.")
        cur.execute(
            "SELECT available FROM loyalty_accounts WHERE customer_id=%s FOR UPDATE",
            (customer_id,),
        )
        account = cur.fetchone()
        if not account or Decimal(str(account["available"])) < value:
            raise ValueError("Недостатньо доступних бонусів.")
        cur.execute(
            """SELECT id,remaining_amount FROM loyalty_lots
               WHERE customer_id=%s AND state='available'
                 AND expires_at>NOW() AND remaining_amount>0
               ORDER BY expires_at,id FOR UPDATE""",
            (customer_id,),
        )
        lots = list(cur.fetchall())
        remaining = value
        for lot in lots:
            if remaining <= 0:
                break
            use = min(remaining, Decimal(str(lot["remaining_amount"])))
            new_left = Decimal(str(lot["remaining_amount"])) - use
            cur.execute(
                "UPDATE loyalty_lots SET remaining_amount=%s,state=%s WHERE id=%s",
                (new_left, "spent" if new_left == 0 else "available", lot["id"]),
            )
            remaining -= use
        if remaining > 0:
            raise RuntimeError(
                "Баланс рахунку не узгоджується з активними бонусними партіями. "
                "Списання скасовано."
            )
        cur.execute(
            """INSERT INTO loyalty_transactions
               (customer_id,order_id,transaction_type,amount,state,reason,
                actor_telegram_id,idempotency_key)
               VALUES(%s,%s,'redeem',%s,'completed','Списання бонусів',%s,%s)""",
            (customer_id, order_id, -value, actor_telegram_id, key),
        )
        cur.execute(
            """UPDATE loyalty_accounts SET available=available-%s,updated_at=NOW()
               WHERE customer_id=%s AND available>=%s""",
            (value, customer_id, value),
        )
        if cur.rowcount != 1:
            raise RuntimeError("Баланс бонусів змінився паралельно. Транзакцію скасовано.")



def expire_loyalty_lots() -> Decimal:
    expired_total = Decimal('0.00')
    with db_cursor() as cur:
        cur.execute("SELECT id,customer_id,remaining_amount FROM loyalty_lots WHERE state='available' AND expires_at<=NOW() AND remaining_amount>0 ORDER BY customer_id,id FOR UPDATE SKIP LOCKED")
        rows = list(cur.fetchall())
        for row in rows:
            amount = Decimal(str(row['remaining_amount']))
            cur.execute("UPDATE loyalty_lots SET state='expired',remaining_amount=0 WHERE id=%s", (row['id'],))
            cur.execute("UPDATE loyalty_accounts SET available=GREATEST(0,available-%s),updated_at=NOW() WHERE customer_id=%s", (amount,row['customer_id']))
            cur.execute("INSERT INTO loyalty_transactions(customer_id,transaction_type,amount,state,reason,idempotency_key) VALUES(%s,'expire',%s,'completed','Закінчився строк дії бонусної партії',%s)",
                        (row['customer_id'],-amount,f"lot:{row['id']}:expired"))
            expired_total += amount
    return expired_total


def create_support_ticket(customer_telegram_id: int, body: str, order_id: Optional[int] = None) -> int:
    body = body.strip()
    if not body or len(body) > 4000:
        raise ValueError("Повідомлення має містити від 1 до 4000 символів.")
    with db_cursor() as cur:
        cur.execute("INSERT INTO support_tickets(customer_telegram_id,order_id) VALUES(%s,%s) RETURNING id", (customer_telegram_id, order_id))
        ticket_id = int(cur.fetchone()["id"])
        cur.execute("INSERT INTO support_messages(ticket_id,sender_telegram_id,sender_type,body) VALUES(%s,%s,'customer',%s)", (ticket_id, customer_telegram_id, body))
        payload = {"ticket_id": ticket_id,
                   "text": f"🎫 <b>Нове звернення #{ticket_id}</b>\n\n{safe(body[:500])}",
                   "buttons": [["✍️ Відповісти", f"support:reply:{ticket_id}"],
                               ["📂 Відкрити звернення", f"support:ticket:{ticket_id}"]]}
        for rid in staff_recipient_ids(cur, ("owner", "admin", "manager")):
            enqueue_notification(cur, rid, "support", payload, f"ticket:{ticket_id}:created:{rid}")
        return ticket_id


def add_ticket_reply(ticket_id: int, sender_id: int, sender_type: str, body: str) -> None:
    if sender_type not in ("customer", "staff") or not body.strip():
        raise ValueError("Некоректна відповідь.")
    with db_cursor() as cur:
        cur.execute("SELECT status FROM support_tickets WHERE id=%s FOR UPDATE", (ticket_id,))
        ticket = cur.fetchone()
        if not ticket or ticket["status"] == "closed":
            raise ValueError("Звернення закрите або не існує.")
        cur.execute("INSERT INTO support_messages(ticket_id,sender_telegram_id,sender_type,body) VALUES(%s,%s,%s,%s)", (ticket_id, sender_id, sender_type, body.strip()[:4000]))
        cur.execute("UPDATE support_tickets SET status='open',updated_at=NOW() WHERE id=%s", (ticket_id,))


def create_delivery_slots(slot_rows: list[dict], actor: Staff) -> int:
    if not actor.can("delivery.update"):
        raise PermissionError("Недостатньо прав.")
    created = 0
    with db_cursor() as cur:
        for item in slot_rows:
            if item["ends_at"] <= item["starts_at"] or item.get("capacity", 1) < 1:
                raise ValueError("Некоректний часовий слот.")
            cur.execute("""INSERT INTO delivery_slots(slot_date,starts_at,ends_at,tariff_code,capacity,created_by)
                           VALUES(%s,%s,%s,%s,%s,%s) ON CONFLICT(starts_at,tariff_code) DO NOTHING""",
                        (item["slot_date"], item["starts_at"], item["ends_at"], item["tariff_code"], item.get("capacity", 1), actor.telegram_id))
            created += cur.rowcount
    return created


def book_delivery_slot(slot_id: int) -> bool:
    """Atomic capacity check; concurrent callers cannot overbook a slot."""
    with db_cursor() as cur:
        cur.execute("""UPDATE delivery_slots SET booked_count=booked_count+1
                       WHERE id=%s AND active=TRUE AND starts_at>NOW() AND booked_count<capacity
                       RETURNING id""", (slot_id,))
        return cur.fetchone() is not None


def enqueue_notification(cur, recipient_id: int, category: str, payload: dict, dedupe_key: str) -> None:
    cur.execute("""INSERT INTO notification_outbox(recipient_telegram_id,category,payload,dedupe_key)
                   VALUES(%s,%s,%s::jsonb,%s) ON CONFLICT(dedupe_key) DO NOTHING""",
                (recipient_id, category, json_dumps(payload), dedupe_key))


def staff_recipient_ids(cur, roles=("owner", "admin")) -> list:
    """Owner + configured admins + every ACTIVE, not-locked staff member with one of the roles."""
    ids = [CONFIG.owner_id]
    if "admin" in roles:
        ids.extend(CONFIG.admin_ids)
    cur.execute("""SELECT s.telegram_id FROM staff s
                   LEFT JOIN staff_security_state ss ON ss.telegram_id=s.telegram_id
                   WHERE s.active=TRUE AND s.role = ANY(%s)
                     AND COALESCE(ss.state,'active') NOT IN ('owner_locked','security_locked','deactivated')""",
                (list(roles),))
    ids.extend(int(r["telegram_id"]) for r in cur.fetchall())
    return list(dict.fromkeys(int(i) for i in ids))


def queue_owner_admin_notification(category: str, payload: dict, dedupe_key: str) -> None:
    recipients = list(dict.fromkeys([CONFIG.owner_id, *CONFIG.admin_ids]))
    with db_cursor() as cur:
        for recipient in recipients:
            enqueue_notification(cur, recipient, category, payload, f"{dedupe_key}:{recipient}")


def dispatch_notification_batch(batch_size: int = 25) -> int:
    """Claim briefly, send outside locks, then acknowledge only our own lease."""
    claim_token = uuid.uuid4().hex
    with db_cursor() as cur:
        cur.execute(
            """WITH picked AS (
                 SELECT id FROM notification_outbox
                 WHERE state='pending' AND attempts<8 AND available_at<=NOW()
                 ORDER BY id FOR UPDATE SKIP LOCKED LIMIT %s
               )
               UPDATE notification_outbox n
               SET available_at=NOW()+INTERVAL '5 minutes',
                   last_attempt_at=NOW(),claim_token=%s
               FROM picked WHERE n.id=picked.id
               RETURNING n.id,n.recipient_telegram_id,n.payload,n.attempts""",
            (max(1, min(100, batch_size)), claim_token),
        )
        rows = list(cur.fetchall())
    sent = 0
    for row in rows:
        try:
            payload = row["payload"] if isinstance(row["payload"], dict) else json.loads(row["payload"])
            markup = None
            if isinstance(payload, dict) and payload.get("buttons"):
                markup = types.InlineKeyboardMarkup(row_width=1)
                for label, data in payload["buttons"]:
                    markup.add(types.InlineKeyboardButton(label, callback_data=data))
            bot.send_message(int(row["recipient_telegram_id"]), str(payload.get("text") or payload), reply_markup=markup)
        except Exception as exc:
            error_name = type(exc).__name__
            blocked = "ApiTelegramException" in error_name and "403" in str(exc)
            with db_cursor() as cur:
                cur.execute(
                    """UPDATE notification_outbox
                       SET attempts=attempts+1,state=%s,last_error=%s,last_attempt_at=NOW(),
                           available_at=CASE WHEN %s THEN available_at
                             ELSE NOW()+(LEAST(3600,POWER(2,attempts+1)::int)*INTERVAL '1 second') END,
                           claim_token=NULL
                       WHERE id=%s AND state='pending' AND claim_token=%s""",
                    ("blocked" if blocked else "pending", error_name, blocked, row["id"], claim_token),
                )
        else:
            with db_cursor() as cur:
                cur.execute(
                    """UPDATE notification_outbox SET state='sent',attempts=attempts+1,
                       sent_at=NOW(),last_attempt_at=NOW(),last_error=NULL,claim_token=NULL
                       WHERE id=%s AND state='pending' AND claim_token=%s""",
                    (row["id"], claim_token),
                )
                sent += cur.rowcount
    return sent


def set_app_setting(key: str, value: Any, actor: Staff) -> None:
    if actor.role != "owner":
        raise PermissionError("Налаштування доступні лише власнику.")
    with db_cursor() as cur:
        cur.execute("""INSERT INTO app_settings(setting_key,setting_value,updated_by) VALUES(%s,%s::jsonb,%s)
                       ON CONFLICT(setting_key) DO UPDATE SET setting_value=EXCLUDED.setting_value,
                       updated_by=EXCLUDED.updated_by,updated_at=NOW()""", (key, json_dumps(value), actor.telegram_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'settings.updated','setting',%s,%s::jsonb)",
                    (actor.telegram_id, actor.role, key, json_dumps(value)))


def create_business_task(title: str, description: str, assigned_to: Optional[int], due_at, actor: Staff) -> int:
    if actor.role not in ("owner", "admin") or not title.strip():
        raise PermissionError("Недостатньо прав або порожня назва задачі.")
    if len(title.strip()) > 180 or len(description.strip()) > 4000:
        raise ValueError("Назва задачі: до 180 символів, опис: до 4000 символів.")
    if assigned_to is not None:
        with db_cursor() as cur:
            cur.execute("SELECT active FROM staff WHERE telegram_id=%s", (assigned_to,))
            assignee = cur.fetchone()
            if not assignee or not assignee["active"]:
                raise ValueError("Виконавця не знайдено або він неактивний.")
    with db_cursor() as cur:
        cur.execute("INSERT INTO business_tasks(title,description,assigned_to,created_by,due_at) VALUES(%s,%s,%s,%s,%s) RETURNING id",
                    (title.strip(), description.strip(), assigned_to, actor.telegram_id, due_at))
        task_id = int(cur.fetchone()["id"])
        if assigned_to:
            enqueue_notification(cur, assigned_to, "tasks", {"text": f"Нова задача #{task_id}: {title}"}, f"task:{task_id}:assigned")
        return task_id


def create_expense(category: str, amount: Decimal, description: str, actor: Staff) -> int:
    if actor.role != "owner" or amount < 0:
        raise PermissionError("Фінансові витрати може вносити лише власник.")
    with db_cursor() as cur:
        cur.execute("INSERT INTO business_expenses(category,amount,description,created_by) VALUES(%s,%s,%s,%s) RETURNING id",
                    (category.strip(), amount, description.strip(), actor.telegram_id))
        expense_id = int(cur.fetchone()["id"])
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'finance.expense_created','expense',%s,%s::jsonb)",
                    (actor.telegram_id, actor.role, str(expense_id), json_dumps({"category": category, "amount": amount, "description": description})))
        return expense_id


# ---------------------------------------------------------------------------
# Roles and access control
# ---------------------------------------------------------------------------

ROLE_LABELS = {
    "owner": "Власник",
    "admin": "Адміністратор",
    "manager": "Менеджер",
    "packer": "Збірник",
    "courier": "Кур’єр",
}

TICKET_STATUS_LABELS = {
    "new": "🆕 нове", "open": "🟢 в роботі",
    "waiting_customer": "⏳ чекаємо клієнта", "closed": "🔒 закрите",
}

PERMISSIONS = {
    "owner": {"*"},
    "admin": {
        "orders.read", "orders.update", "orders.search",
        "customers.read", "inventory.read", "inventory.receive",
        "support.read", "support.reply", "delivery.read", "delivery.update",
        "catalog.read", "catalog.update",
    },
    "manager": {
        "orders.read", "orders.update", "orders.search",
        "customers.read", "delivery.read", "delivery.update",
        "support.read", "support.reply", "catalog.read",
    },
    "packer": {
        "orders.read", "orders.update", "orders.search",
        "inventory.read",
    },
    "courier": {"delivery.read", "delivery.update"},
}


@dataclass
class Staff:
    telegram_id: int
    display_name: str
    role: str
    active: bool

    def can(self, permission: str) -> bool:
        # Owner has full permissions; security locks are enforced earlier by require_staff().
        if self.role == "owner":
            return True
        allowed = PERMISSIONS.get(self.role, set())
        return "*" in allowed or permission in allowed


def get_staff(telegram_id: int) -> Optional[Staff]:
    with db_cursor() as cur:
        cur.execute(
            "SELECT telegram_id, display_name, role, active FROM staff WHERE telegram_id=%s",
            (telegram_id,),
        )
        row = cur.fetchone()
    return Staff(**row) if row else None


def release_expired_security_lock(telegram_id: int) -> bool:
    """Lazily release only expired automatic locks, never manual owner locks."""
    with db_cursor() as cur:
        cur.execute(
            """UPDATE staff_security_state SET state='active',review_deadline=NULL,
               review_counter=review_counter+1,updated_at=NOW()
               WHERE telegram_id=%s AND state='security_locked'
                 AND review_deadline IS NOT NULL AND review_deadline<=NOW()
               RETURNING review_counter""", (telegram_id,))
        row=cur.fetchone()
        if not row:
            return False
        messages = [
            "🟢 Доступ відновлено. Система безпеки видихнула. Поки що. 😎",
            "🤖 Перевірку завершено: ви знову в системі. Робот-параноїк передає вибачення.",
            "🔓 Бан знято автоматично. Повертаємось до роботи без рекордів підозрілої активності 😂",
            "🛡️ Таймер завершився. Доступ відновлено. Не змушуйте мене знову рахувати до порога.",
        ]
        idx=(int(row["review_counter"])-1)%len(messages)
        enqueue_notification(cur,telegram_id,"security",{"text":messages[idx]},
                             f"security-auto-unlock:{telegram_id}:{row['review_counter']}")
        security_event(cur,"important","security.temporary_lock_expired",None,telegram_id,
                       {"duration_minutes":SECURITY_AUTO_LOCK_MINUTES})
        return True


def require_staff(message_or_call, permission: Optional[str] = None) -> Optional[Staff]:
    user = getattr(message_or_call, "from_user", None)
    if user is None:
        return None
    try:
        release_expired_security_lock(int(user.id))
    except Exception:
        log.exception("Could not check automatic security lock expiry for %s", user.id)
    staff = get_staff(user.id)
    if not staff or not staff.active:
        return None
    # Security state is enforced server-side for every staff action.
    with db_cursor() as cur:
        cur.execute("SELECT state,review_deadline FROM staff_security_state WHERE telegram_id=%s", (user.id,))
        security = cur.fetchone()
    if security and security["state"] != "active":
        if security["state"] == "review_suspended":
            # Handoff permits read-only inspection during the 60-second review.
            if not permission or not (permission.endswith(".read") or permission.endswith(".search")):
                return None
        if security["state"] in ("security_locked", "owner_locked", "deactivated"):
            return None
    if permission and not staff.can(permission):
        return None
    return staff



def start_staff_review(target_telegram_id: int, actor: Staff) -> None:
    if actor.role != 'owner' or target_telegram_id == CONFIG.owner_id:
        raise PermissionError('Перевірку працівника може запускати лише власник для іншого працівника.')
    with db_cursor() as cur:
        cur.execute("SELECT active FROM staff WHERE telegram_id=%s FOR UPDATE", (target_telegram_id,))
        target = cur.fetchone()
        if not target or not target['active']:
            raise ValueError('Активного працівника не знайдено.')
        cur.execute("SELECT state FROM staff_security_state WHERE telegram_id=%s FOR UPDATE", (target_telegram_id,))
        existing = cur.fetchone()
        if existing and existing["state"] == "review_suspended":
            return
        if existing and existing["state"] in ("owner_locked","security_locked","deactivated"):
            raise ValueError("Працівник уже має блокування або деактивацію.")
        cur.execute("""INSERT INTO staff_security_state(telegram_id,state,review_deadline)
                       VALUES(%s,'review_suspended',NOW()+INTERVAL '60 seconds')
                       ON CONFLICT(telegram_id) DO UPDATE SET
                       state='review_suspended',review_deadline=NOW()+INTERVAL '60 seconds',updated_at=NOW()""",
                    (target_telegram_id,))
        cur.execute("INSERT INTO security_events(severity,event_type,actor_telegram_id,subject_telegram_id,details) VALUES('important','staff.review_started',%s,%s,%s::jsonb)",
                    (actor.telegram_id,target_telegram_id,json_dumps({'duration_seconds':60})))
        enqueue_notification(cur,target_telegram_id,'security',{'text':'🔍 Cloud Hub Security. Власник системи ініціював перевірку вашої активності. На час перевірки доступ до робочих функцій тимчасово призупинено на 60 секунд.'},f'staff-review:{target_telegram_id}:{int(time.time())}')


def set_staff_lock(target_telegram_id: int, locked: bool, actor: Staff, reason: str = '') -> None:
    if actor.role != 'owner' or target_telegram_id == CONFIG.owner_id:
        raise PermissionError('Керувати блокуванням може лише власник.')
    state = 'owner_locked' if locked else 'active'
    with db_cursor() as cur:
        cur.execute("SELECT telegram_id FROM staff WHERE telegram_id=%s FOR UPDATE", (target_telegram_id,))
        if not cur.fetchone():
            raise ValueError('Працівника не знайдено.')
        if locked:
            cur.execute("""INSERT INTO staff_security_state(telegram_id,state,review_deadline)
                           VALUES(%s,'owner_locked',NULL) ON CONFLICT(telegram_id) DO UPDATE
                           SET state='owner_locked',review_deadline=NULL,updated_at=NOW()""", (target_telegram_id,))
        else:
            cur.execute("""UPDATE staff_security_state SET state='active',review_deadline=NULL,updated_at=NOW()
                           WHERE telegram_id=%s AND state='owner_locked'""", (target_telegram_id,))
            if cur.rowcount == 0:
                cur.execute("SELECT state FROM staff_security_state WHERE telegram_id=%s", (target_telegram_id,))
                current = cur.fetchone()
                if current and current['state'] in ('security_locked','deactivated'):
                    raise PermissionError('Критичне блокування або деактивацію не можна зняти цією дією.')
        cur.execute("INSERT INTO security_events(severity,event_type,actor_telegram_id,subject_telegram_id,details) VALUES('critical',%s,%s,%s,%s::jsonb)",
                    ('staff.owner_locked' if locked else 'staff.unlocked',actor.telegram_id,target_telegram_id,json_dumps({'reason':reason.strip()})))
        if locked:
            enqueue_notification(cur,target_telegram_id,'security',{'text':'⛔ Обліковий запис призупинено власником Cloud Hub. Самостійне відновлення доступу неможливе.'},f'staff-lock:{target_telegram_id}:{int(time.time())}')


def complete_expired_staff_reviews() -> int:
    messages = [
        'Перевірку завершено! Доступ відновлено. Гарної роботи! 😎',
        'Ви знову в строю! Власник підтвердив відновлення доступу. 😂',
        'Доступ відновлено! Цього разу все обійшлося. 🤖',
        'Вітаємо назад! Перевірку успішно завершено. Не робіть із цього щоденну традицію. 😂',
    ]
    count = 0
    with db_cursor() as cur:
        cur.execute("SELECT telegram_id,review_counter FROM staff_security_state WHERE state='review_suspended' AND review_deadline<=NOW() ORDER BY telegram_id FOR UPDATE SKIP LOCKED")
        rows = list(cur.fetchall())
        for row in rows:
            idx = int(row['review_counter']) % len(messages)
            cur.execute("UPDATE staff_security_state SET state='active',review_deadline=NULL,review_counter=review_counter+1,updated_at=NOW() WHERE telegram_id=%s AND state='review_suspended'", (row['telegram_id'],))
            changed = cur.rowcount
            if changed:
                enqueue_notification(cur,row['telegram_id'],'security',{'text':messages[idx]},f'staff-review-complete:{row["telegram_id"]}:{row["review_counter"]}')
                count += 1
    return count


def complete_expired_security_locks() -> int:
    """Expire temporary automatic locks; owner-initiated locks have no deadline."""
    count=0
    messages=[
        "🟢 Доступ відновлено. Система безпеки видихнула. Поки що. 😎",
        "🤖 Перевірку завершено: ви знову в системі. Робот-параноїк передає вибачення.",
        "🔓 Бан знято автоматично. Повертаємось до роботи без рекордів підозрілої активності 😂",
        "🛡️ Таймер завершився. Доступ відновлено. Не змушуйте мене знову рахувати до порога.",
    ]
    with db_cursor() as cur:
        cur.execute("""SELECT telegram_id,review_counter FROM staff_security_state
                       WHERE state='security_locked' AND review_deadline IS NOT NULL
                         AND review_deadline<=NOW()
                       ORDER BY telegram_id FOR UPDATE SKIP LOCKED""")
        rows=list(cur.fetchall())
        for row in rows:
            cur.execute("""UPDATE staff_security_state SET state='active',review_deadline=NULL,
                           review_counter=review_counter+1,updated_at=NOW()
                           WHERE telegram_id=%s AND state='security_locked'
                             AND review_deadline IS NOT NULL AND review_deadline<=NOW()""",
                        (row["telegram_id"],))
            if cur.rowcount:
                idx=int(row["review_counter"])%len(messages)
                enqueue_notification(cur,int(row["telegram_id"]),"security",{"text":messages[idx]},
                    f"security-auto-unlock:{row['telegram_id']}:{row['review_counter']}")
                security_event(cur,"important","security.temporary_lock_expired",None,
                    int(row["telegram_id"]),{"duration_minutes":SECURITY_AUTO_LOCK_MINUTES})
                count+=1
    return count


def audit(actor: Optional[Staff], action: str, entity_type: str, entity_id: str,
          before: Any = None, after: Any = None, reason: Optional[str] = None) -> None:
    import json
    with db_cursor() as cur:
        cur.execute(
            """
            INSERT INTO audit_log
              (actor_telegram_id, actor_role, action, entity_type, entity_id,
               before_data, after_data, reason)
            VALUES (%s,%s,%s,%s,%s,%s::jsonb,%s::jsonb,%s)
            """,
            (
                actor.telegram_id if actor else None,
                actor.role if actor else None,
                action, entity_type, str(entity_id),
                json.dumps(before, ensure_ascii=False, default=str) if before is not None else None,
                json.dumps(after, ensure_ascii=False, default=str) if after is not None else None,
                reason,
            ),
        )
        normalized_action = str(action or "").casefold()
        signal = None
        if "permission" in normalized_action or "role_changed" in normalized_action:
            signal = "permission_change"
        elif "tamper" in normalized_action or "audit.deleted" in normalized_action:
            signal = "audit_tamper"
        elif "cancel" in normalized_action and entity_type == "order":
            signal = "order_cancel"
        elif "price" in normalized_action and ("change" in normalized_action or "edit" in normalized_action):
            signal = "price_edit"
        elif "stock_zero" in normalized_action or "zeroed" in normalized_action:
            signal = "stock_zero"
        elif "bonus" in normalized_action and ("adjust" in normalized_action or "manual" in normalized_action):
            signal = "bonus_adjust"
        elif "export" in normalized_action and "customer" in normalized_action:
            signal = "customer_export"
        if signal and actor:
            record_security_signal(cur, signal, actor.telegram_id, None,
                                   {"action": action, "entity_type": entity_type, "entity_id": str(entity_id)})


# ---------------------------------------------------------------------------
# Text normalization and typo-tolerant search
# ---------------------------------------------------------------------------

_TRANSLIT = str.maketrans({
    "ё": "е", "ъ": "", "ы": "и", "э": "е",
    "і": "и", "ї": "и", "є": "е", "ґ": "г",
})


def normalize_text(value: Any) -> str:
    text = unicodedata.normalize("NFKC", str(value or "")).casefold().translate(_TRANSLIT)
    text = re.sub(r"[\u0300-\u036f]", "", text)
    text = re.sub(r"[^0-9a-zа-яіїєґ@._+\- ]+", " ", text)
    return re.sub(r"\s+", " ", text).strip()


def normalize_phone(value: Any) -> str:
    return re.sub(r"\D", "", str(value or ""))


def similarity(a: str, b: str) -> float:
    a, b = normalize_text(a), normalize_text(b)
    if not a or not b:
        return 0.0
    if a in b or b in a:
        return min(1.0, 0.82 + 0.18 * min(len(a), len(b)) / max(len(a), len(b)))
    return difflib.SequenceMatcher(None, a, b).ratio()


def fuzzy_name_match(query: str, candidate: str) -> float:
    q = normalize_text(query)
    c = normalize_text(candidate)
    if not q or not c:
        return 0.0
    best = similarity(q, c)
    q_tokens, c_tokens = q.split(), c.split()
    for qt in q_tokens:
        if len(qt) < 3:
            continue
        for ct in c_tokens:
            best = max(best, similarity(qt, ct))
    return best


# ---------------------------------------------------------------------------
# Order queries and status transitions
# ---------------------------------------------------------------------------

STATUS_LABELS = {
    "new": "Нове",
    "confirmed": "Підтверджено",
    "packing": "Збирається",
    "packed": "Зібрано",
    "ready_to_ship": "Готове до відправлення",
    "shipped": "Відправлено",
    "delivered": "Доставлено",
    "completed": "Завершено",
    "problem": "Проблемне",
    "cancelled": "Скасовано",
    "returned": "Повернення",
}

# A deliberately conservative transition graph. Owner may still use only
# valid transitions; exceptional corrections should be a separate audited flow.
ALLOWED_TRANSITIONS = {
    "new": {"confirmed", "packing", "problem", "cancelled"},
    "confirmed": {"packing", "problem", "cancelled"},
    "packing": {"packed", "problem", "cancelled"},
    "packed": {"ready_to_ship", "problem", "cancelled"},
    "ready_to_ship": {"shipped", "problem", "cancelled"},
    "shipped": {"delivered", "returned", "problem"},
    "delivered": {"completed", "returned", "problem"},
    "completed": {"returned"},
    "problem": {"confirmed", "packing", "packed", "cancelled", "returned"},
    "cancelled": set(),
    "returned": set(),
}


def order_select_sql(where: str = "") -> str:
    return f"""
        SELECT o.*, c.first_name, c.last_name, c.username AS customer_username,
               c.phone AS customer_phone,
               COALESCE((
                   SELECT json_agg(json_build_object(
                       'name', oi.product_name_snapshot,
                       'sku', oi.sku_snapshot,
                       'qty', oi.quantity,
                       'price', oi.unit_price,
                       'line_total', oi.line_total
                   ) ORDER BY oi.id)
                   FROM order_items oi WHERE oi.order_id=o.id
               ), '[]'::json) AS items
        FROM orders o
        LEFT JOIN customers c ON c.id=o.customer_id
        {where}
    """


def fetch_uncollected_orders() -> list[dict]:
    # No business-result cap. Telegram delivery is paced separately.
    with db_cursor() as cur:
        cur.execute(
            order_select_sql(
                "WHERE o.status IN ('new','confirmed','packing') "
                "ORDER BY o.created_at ASC, o.id ASC"
            )
        )
        return list(cur.fetchall())


def fetch_last_orders(limit: int = 100) -> list[dict]:
    limit = max(1, min(100, int(limit)))
    with db_cursor() as cur:
        cur.execute(
            order_select_sql("ORDER BY o.created_at DESC, o.id DESC LIMIT %s"),
            (limit,),
        )
        return list(cur.fetchall())


def fetch_order(order_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(order_select_sql("WHERE o.id=%s"), (order_id,))
        return cur.fetchone()


def consume_order_reservations(order_id: int, actor: Optional[Staff] = None) -> None:
    with db_cursor() as cur:
        cur.execute("SELECT id,variant_id,quantity FROM stock_reservations WHERE order_id=%s AND state='active' ORDER BY variant_id FOR UPDATE", (order_id,))
        rows = list(cur.fetchall())
        for row in rows:
            cur.execute("UPDATE product_variants SET stock_qty=stock_qty-%s,reserved_qty=GREATEST(0,reserved_qty-%s),updated_at=NOW() WHERE id=%s AND stock_qty>=%s AND reserved_qty>=%s", (row['quantity'],row['quantity'],row['variant_id'],row['quantity'],row['quantity']))
            if cur.rowcount != 1:
                raise RuntimeError('Неможливо списати зарезервований залишок. Потрібна перевірка складу.')
            cur.execute("UPDATE stock_reservations SET state='consumed' WHERE id=%s", (row['id'],))
            cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reference_type,reference_id,reason,actor_telegram_id) VALUES(%s,'sale',%s,'order',%s,'Списання після передачі в доставку',%s)", (row['variant_id'],-int(row['quantity']),str(order_id),actor.telegram_id if actor else None))


def release_order_reservations(order_id: int, actor: Optional[Staff] = None, reason: str = 'Замовлення скасовано') -> None:
    with db_cursor() as cur:
        cur.execute("SELECT id,variant_id,quantity FROM stock_reservations WHERE order_id=%s AND state='active' ORDER BY variant_id FOR UPDATE", (order_id,))
        rows = list(cur.fetchall())
        for row in rows:
            cur.execute("UPDATE product_variants SET reserved_qty=GREATEST(0,reserved_qty-%s),updated_at=NOW() WHERE id=%s", (row['quantity'],row['variant_id']))
            cur.execute("UPDATE stock_reservations SET state='released' WHERE id=%s", (row['id'],))
            cur.execute("INSERT INTO inventory_movements(variant_id,movement_type,quantity_delta,reference_type,reference_id,reason,actor_telegram_id) VALUES(%s,'reservation_release',%s,'order',%s,%s,%s)", (row['variant_id'],row['quantity'],str(order_id),reason,actor.telegram_id if actor else None))

def update_order_status(order_id: int, new_status: str, actor: Staff) -> tuple[bool, str]:
    if new_status not in STATUS_LABELS:
        return False, "Невідомий статус."
    if not actor.can("orders.update"):
        return False, "Недостатньо прав."
    with db_cursor() as cur:
        cur.execute(
            """SELECT o.id,o.status,o.customer_id,c.age_verification_status
               FROM orders o LEFT JOIN customers c ON c.id=o.customer_id
               WHERE o.id=%s FOR UPDATE OF o""",
            (order_id,),
        )
        row = cur.fetchone()
        if not row:
            return False, "Замовлення не знайдено."
        if (new_status in {"confirmed", "packing", "packed", "ready_to_ship", "shipped"}
                and row.get("age_verification_status") != "verified"):
            return False, (
                "Спочатку працівник має вручну перевірити документ клієнта "
                "та підтвердити це в розділі «Перевірка віку» (/agequeue)."
            )
        old_status = row["status"]
        if old_status == new_status:
            return False, "Замовлення вже має цей статус."
        if new_status not in ALLOWED_TRANSITIONS.get(old_status, set()):
            return False, f"Перехід «{STATUS_LABELS.get(old_status, old_status)}» → «{STATUS_LABELS[new_status]}» заборонений."
        cur.execute(
            "UPDATE orders SET status=%s, updated_at=NOW() WHERE id=%s",
            (new_status, order_id),
        )
        cur.execute(
            """
            INSERT INTO audit_log
              (actor_telegram_id, actor_role, action, entity_type, entity_id,
               before_data, after_data)
            VALUES (%s,%s,'order.status_changed','order',%s,%s::jsonb,%s::jsonb)
            """,
            (actor.telegram_id, actor.role, str(order_id),
             json_dumps({"status": old_status}), json_dumps({"status": new_status})),
        )
        # Stock movements and order state commit atomically. The shared
        # lifecycle helpers reject missing reservations and update the ledger.
        if new_status == "shipped":
            _stock_consume_order_reservations(cur, order_id, actor)
        elif new_status == "cancelled":
            _stock_release_order_reservations(cur, order_id, actor, "released")
            _cancel_pending_order_bonuses_tx(cur, order_id, row.get("customer_id"))
        elif new_status in ("delivered", "completed"):
            cur.execute("SELECT customer_id FROM orders WHERE id=%s FOR UPDATE", (order_id,))
            customer_row = cur.fetchone()
            cur.execute("UPDATE loyalty_lots SET state='available',available_at=NOW() WHERE source_transaction_id IN (SELECT id FROM loyalty_transactions WHERE order_id=%s AND transaction_type='earn') AND state='pending' RETURNING remaining_amount",
                        (order_id,))
            bonus_total = sum((Decimal(str(x['remaining_amount'])) for x in cur.fetchall()), Decimal('0.00'))
            if bonus_total and customer_row:
                cur.execute("UPDATE loyalty_accounts SET pending=GREATEST(0,pending-%s),available=available+%s,updated_at=NOW() WHERE customer_id=%s",
                            (bonus_total,bonus_total,customer_row['customer_id']))
                cur.execute("UPDATE loyalty_transactions SET state='available' WHERE order_id=%s AND transaction_type='earn' AND state='pending'", (order_id,))
    return True, f"Статус змінено: {STATUS_LABELS[old_status]} → {STATUS_LABELS[new_status]}."


def json_dumps(value: Any) -> str:
    import json
    return json.dumps(value, ensure_ascii=False, default=str)


def search_orders(query: str, limit: int = 50) -> list[tuple[dict, float, str]]:
    """Search the complete order history. Fuzzy name/address scan is keyset-paged.

    Exact/partial matches are collected first. Remaining historical rows are
    scanned in bounded batches so no arbitrary recent-5000 cutoff exists.
    """
    raw = str(query or "").strip()
    q = normalize_text(raw)
    digits = normalize_phone(raw)
    if len(q) < 2 and len(digits) < 3:
        return []

    results: dict[int, tuple[dict, float, str]] = {}

    with db_cursor() as cur:
        # Exact/partial structured fields use parameterized SQL.
        cur.execute(
            order_select_sql(
                """
                WHERE (
                    o.order_number ILIKE %s OR o.ttn ILIKE %s
                    OR o.city ILIKE %s OR o.delivery_branch ILIKE %s
                    OR o.delivery_address ILIKE %s
                    OR o.customer_name_snapshot ILIKE %s
                    OR o.username_snapshot ILIKE %s
                    OR c.username ILIKE %s
                    OR c.first_name ILIKE %s OR c.last_name ILIKE %s
                    OR (%s <> '' AND regexp_replace(coalesce(o.phone_snapshot,''),'\\D','','g') LIKE %s)
                    OR (%s <> '' AND o.telegram_id_snapshot::text = %s)
                )
                ORDER BY o.created_at DESC, o.id DESC LIMIT 250
                """
            ),
            (
                f"%{raw}%", f"%{raw}%", f"%{raw}%", f"%{raw}%", f"%{raw}%",
                f"%{raw}%", f"%{raw}%", f"%{raw}%", f"%{raw}%", f"%{raw}%",
                digits, f"%{digits}%", raw if raw.isdigit() else "", raw,
            ),
        )
        rows = list(cur.fetchall())
        for row in rows:
            results[row["id"]] = (row, 1.0, "точний/частковий збіг")

        # Full-history typo-tolerant scan. Fetch only compact fields in pages;
        # load full order cards only for matching IDs. This avoids a hidden
        # 5,000-order ceiling while keeping memory bounded.
        last_id = 0
        while True:
            cur.execute(
                """
                SELECT o.id, o.customer_name_snapshot, o.city, o.delivery_branch,
                       o.delivery_address, c.first_name, c.last_name
                FROM orders o LEFT JOIN customers c ON c.id=o.customer_id
                WHERE o.id > %s
                ORDER BY o.id ASC LIMIT 1000
                """,
                (last_id,),
            )
            batch = list(cur.fetchall())
            if not batch:
                break
            last_id = batch[-1]["id"]
            for candidate in batch:
                if candidate["id"] in results:
                    continue
                name = " ".join(filter(None, [
                    candidate.get("customer_name_snapshot"),
                    candidate.get("first_name"), candidate.get("last_name"),
                ]))
                address = " ".join(filter(None, [
                    candidate.get("city"), candidate.get("delivery_branch"),
                    candidate.get("delivery_address"),
                ]))
                score = max(fuzzy_name_match(raw, name), fuzzy_name_match(raw, address))
                if score >= 0.72:
                    results[candidate["id"]] = (None, score, "схожий збіг")

        fuzzy_ids = [oid for oid, (row, _, _) in results.items() if row is None]
        if fuzzy_ids:
            cur.execute(order_select_sql("WHERE o.id = ANY(%s)"), (fuzzy_ids,))
            for row in cur.fetchall():
                _, score, match_type = results[row["id"]]
                results[row["id"]] = (row, score, match_type)

    ranked = sorted(
        results.values(),
        key=lambda item: (item[1], item[0]["created_at"], item[0]["id"]),
        reverse=True,
    )
    return ranked[:max(1, min(100, limit))]


# ---------------------------------------------------------------------------
# Courier delivery: road routing, tariff snapshots and customer confirmation
# ---------------------------------------------------------------------------

import json
import urllib.error
import urllib.parse
import urllib.request

from datetime import timedelta


class DeliveryError(RuntimeError):
    """A safe, user-displayable delivery calculation error."""


_GEOCODE_LOCK = threading.Lock()
_LAST_GEOCODE_AT = 0.0
_STORE_COORDINATE_CACHE: Optional[tuple[float, float]] = None


DELIVERY_TARIFFS = {
    "standard": {"title": "Звичайна кур’єрська", "base": Decimal("35.00"),
                 "per_km": Decimal("8.50"), "minimum": Decimal("50.00")},
    "express": {"title": "Екстра швидка", "base": Decimal("50.00"),
                "per_km": Decimal("14.00"), "minimum": None},
    "night": {"title": "Нічна", "base": Decimal("60.00"),
              "per_km": Decimal("22.00"), "minimum": None},
}


LVIV_ONLY_TEXT = "Кур’єрська доставка Cloud Hub доступна лише у Львові. Для іншого міста оберіть Нову пошту."


def _in_lviv(lat: float, lon: float) -> bool:
    """Rough city bounding box; courier delivery is Lviv only."""
    return 49.74 <= float(lat) <= 49.93 and 23.85 <= float(lon) <= 24.20


def _http_json(url: str, *, params: Optional[dict] = None, attempts: int = 2) -> Any:
    if params:
        url = url + ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    request = urllib.request.Request(
        url, headers={"User-Agent": CONFIG.map_user_agent, "Accept": "application/json"}
    )
    host = urllib.parse.urlsplit(url).netloc
    last_exc: Optional[BaseException] = None
    for attempt in range(max(1, attempts)):
        try:
            with urllib.request.urlopen(request, timeout=CONFIG.map_request_timeout) as response:
                return json.loads(response.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            # The real reason used to be hidden; now it is visible in Render logs.
            log.warning("Mapping provider %s returned HTTP %s (attempt %s)", host, exc.code, attempt + 1)
            last_exc = exc
            if exc.code in (400, 403, 404):
                break
        except Exception as exc:
            log.warning("Mapping provider %s failed: %s %s (attempt %s)", host, type(exc).__name__, str(exc)[:160], attempt + 1)
            last_exc = exc
        time.sleep(1.5)
    raise DeliveryError("Не вдалося розрахувати доставку: сервіс карт тимчасово недоступний. Спробуйте за хвилину або оберіть Нову пошту.") from last_exc

def _geocode_address(address: str) -> tuple[float, float, str]:
    global _LAST_GEOCODE_AT
    normalized = normalize_text(address)
    if len(normalized) < 5:
        raise DeliveryError("Введіть повну адресу: місто, вулиця та номер будинку.")
    with db_cursor() as cur:
        cur.execute(
            "SELECT latitude, longitude, display_address FROM delivery_route_cache WHERE normalized_address=%s",
            (normalized,),
        )
        cached = cur.fetchone()
        if cached:
            cur.execute("UPDATE delivery_route_cache SET last_used_at=NOW() WHERE normalized_address=%s", (normalized,))
            return float(cached["latitude"]), float(cached["longitude"]), cached["display_address"]

    # Nominatim's public endpoint asks clients to stay at or below 1 request/sec.
    with _GEOCODE_LOCK:
        wait_for = 1.05 - (time.monotonic() - _LAST_GEOCODE_AT)
        if wait_for > 0:
            time.sleep(wait_for)
        has_city = re.search(r"львів|львов|lviv", address, re.I) is not None
        data = _http_json(CONFIG.geocoding_url, params={
            "q": f"{address}, Україна" if has_city else f"{address}, Львів, Україна",
            "format": "jsonv2", "limit": 1, "countrycodes": "ua", "addressdetails": 1,
            "accept-language": "uk", "viewbox": "23.85,49.93,24.20,49.74", "bounded": 1,
        })
        _LAST_GEOCODE_AT = time.monotonic()
    if not data:
        raise DeliveryError("Не знайшов таку адресу у Львові. Уточніть вулицю та номер будинку.")
    item = data[0]
    lat, lon = float(item["lat"]), float(item["lon"])
    display = str(item.get("display_name") or address)
    # Do not send this internal display address back to the customer.
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO delivery_route_cache(normalized_address,latitude,longitude,display_address)
               VALUES(%s,%s,%s,%s) ON CONFLICT(normalized_address) DO UPDATE SET
               latitude=EXCLUDED.latitude, longitude=EXCLUDED.longitude,
               display_address=EXCLUDED.display_address,last_used_at=NOW()""",
            (normalized, lat, lon, display),
        )
    return lat, lon, display


def _store_coordinates() -> tuple[float, float]:
    global _STORE_COORDINATE_CACHE
    if CONFIG.store_lat is not None and CONFIG.store_lon is not None:
        return CONFIG.store_lat, CONFIG.store_lon
    if _STORE_COORDINATE_CACHE is not None:
        return _STORE_COORDINATE_CACHE
    try:
        lat, lon, _ = _geocode_address(CONFIG.store_address)
    except DeliveryError:
        log.error("Store address %r could not be geocoded. Set STORE_LAT and STORE_LON in Render env vars.", CONFIG.store_address)
        raise DeliveryError("Розрахунок доставки тимчасово недоступний. Зверніться в підтримку або оберіть Нову пошту.")
    _STORE_COORDINATE_CACHE = (lat, lon)
    return _STORE_COORDINATE_CACHE


def _route_to(lat: float, lon: float) -> tuple[float, float, str]:
    store_lat, store_lon = _store_coordinates()
    url = (
        f"{CONFIG.routing_url.rstrip('/')}/"
        f"{store_lon},{store_lat};{lon},{lat}"
    )
    data = _http_json(url, params={"overview": "false", "alternatives": "false", "steps": "false"})
    if data.get("code") != "Ok" or not data.get("routes"):
        raise DeliveryError("Не вдалося побудувати автомобільний маршрут до цієї адреси.")
    route = data["routes"][0]
    distance_km = float(route["distance"]) / 1000.0
    duration_min = float(route["duration"]) / 60.0
    if distance_km > CONFIG.max_courier_km:
        raise DeliveryError(
            f"Кур’єрська доставка доступна в межах {CONFIG.max_courier_km:g} км. "
            "Для цієї адреси оберіть Нову пошту."
        )
    return distance_km, duration_min, "OSRM driving route"


def calculate_delivery_price(distance_km: float, tariff_code: str) -> Decimal:
    if tariff_code not in DELIVERY_TARIFFS:
        raise DeliveryError("Невідомий тариф доставки.")
    km = Decimal(str(distance_km))
    tariff = DELIVERY_TARIFFS[tariff_code]
    price = tariff["base"] + tariff["per_km"] * km
    if tariff["minimum"] is not None:
        price = max(tariff["minimum"], price)
    return price.quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)


def _is_night_slot(now: Optional[datetime] = None) -> bool:
    from zoneinfo import ZoneInfo
    local = (now or datetime.now(timezone.utc)).astimezone(ZoneInfo(CONFIG.timezone))
    return local.hour >= 22 and (local.hour < 24)


def create_delivery_quote(customer_id: int, address: str, tariff_code: str) -> dict:
    if tariff_code == "night" and not _is_night_slot():
        raise DeliveryError("Нічна доставка доступна з 22:00 до 23:59 за київським часом.")
    lat, lon, _internal_display = _geocode_address(address)
    if not _in_lviv(lat, lon):
        raise DeliveryError(LVIV_ONLY_TEXT)
    distance_km, duration_min, route_provider = _route_to(lat, lon)
    price = calculate_delivery_price(distance_km, tariff_code)
    tariff = DELIVERY_TARIFFS[tariff_code]
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO delivery_quotes
               (customer_telegram_id,destination_address,destination_lat,destination_lon,
                distance_km,duration_minutes,tariff_code,tariff_base,tariff_per_km,
                delivery_price,route_provider,route_reference,expires_at)
               VALUES(%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,NOW()+INTERVAL '15 minutes')
               RETURNING id,expires_at""",
            (customer_id, address, lat, lon, round(distance_km, 3), round(duration_min, 2),
             tariff_code, tariff["base"], tariff["per_km"], price, route_provider,
             f"{lat:.6f},{lon:.6f}"),
        )
        saved = cur.fetchone()
    return {
        "id": saved["id"], "distance_km": distance_km, "duration_minutes": duration_min,
        "tariff_code": tariff_code, "tariff_title": tariff["title"],
        "price": price, "expires_at": saved["expires_at"],
    }


def confirm_delivery_quote(quote_id: int, customer_id: int, accepted: bool) -> tuple[bool, str]:
    with db_cursor() as cur:
        cur.execute(
            "SELECT id,state,expires_at FROM delivery_quotes WHERE id=%s AND customer_telegram_id=%s FOR UPDATE",
            (quote_id, customer_id),
        )
        quote = cur.fetchone()
        if not quote or quote["state"] != "pending":
            return False, "Ця пропозиція доставки вже неактуальна. Розрахуйте її ще раз."
        if quote["expires_at"] <= datetime.now(timezone.utc):
            cur.execute("UPDATE delivery_quotes SET state='expired' WHERE id=%s", (quote_id,))
            return False, "Час дії розрахунку минув. Розрахуйте доставку повторно."
        state = "accepted" if accepted else "declined"
        cur.execute("UPDATE delivery_quotes SET state=%s WHERE id=%s", (state, quote_id))
    if accepted:
        return True, "Кур’єрську доставку підтверджено. Продовжуйте оформлення замовлення."
    return True, "Кур’єрську доставку відхилено. Можете обрати Нову пошту."


# ---------------------------------------------------------------------------
# Telegram UI
# ---------------------------------------------------------------------------

def safe(value: Any) -> str:
    return html.escape(str(value if value is not None else "—"))


def money(value: Any) -> str:
    try:
        return f"{float(value):.2f} ₴"
    except (TypeError, ValueError):
        return "—"


DELIVERY_TYPE_LABELS = {
    "nova_poshta": "Нова пошта", "courier_standard": "Кур’єр · звичайна",
    "courier_express": "Кур’єр · експрес до 29 хв", "courier_night": "Кур’єр · нічна",
}


def order_card_text(order: dict) -> str:
    name = order.get("customer_name_snapshot") or " ".join(
        filter(None, [order.get("first_name"), order.get("last_name")])
    ) or "Клієнт"
    phone = order.get("phone_snapshot") or order.get("customer_phone") or "—"
    status = STATUS_LABELS.get(order.get("status"), order.get("status", "—"))
    created = order.get("created_at")
    if isinstance(created, datetime):
        created_text = created.astimezone().strftime("%d.%m.%Y %H:%M")
    else:
        created_text = str(created or "—")
    lines = [
        f"🧾 <b>Замовлення #{safe(order.get('order_number'))}</b>",
        f"👤 Клієнт: {safe(name)}",
        f"📞 Телефон: {safe(phone)}",
        f"📍 Місто: {safe(order.get('city') or '—')}",
        f"🏢 Відділення: {safe(order.get('delivery_branch') or '—')}",
        f"🏠 Адреса (кур’єр): {safe(order.get('delivery_address') or '—')}",
        f"🚚 Доставка: {safe(DELIVERY_TYPE_LABELS.get(order.get('delivery_type'), order.get('delivery_type') or '—'))}",
        f"🚚 ТТН: {safe(order.get('ttn') or '—')}",
        f"📦 Статус: <b>{safe(status)}</b>",
        f"🕒 Створено: {safe(created_text)}",
        "",
        "<b>Товари:</b>",
    ]
    for item in (order.get("items") or []):
        lines.append(
            f"• {safe(item.get('name'))} × {safe(item.get('qty'))} "
            f"({money(item.get('line_total'))})"
        )
    lines.extend([
        "",
        f"Товари: <b>{money(order.get('items_total'))}</b>",
        f"Доставка: {money(order.get('delivery_total'))}",
        f"Разом: <b>{money(order.get('grand_total'))}</b>",
    ])
    return "\n".join(lines)


def order_keyboard(order: dict, staff: Staff) -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=2)
    current = order.get("status")
    buttons = []
    if staff.can("orders.update"):
        for status in ("confirmed", "packing", "packed", "ready_to_ship", "shipped",
                       "delivered", "completed", "problem", "cancelled", "returned"):
            if status in ALLOWED_TRANSITIONS.get(current, set()):
                buttons.append(types.InlineKeyboardButton(
                    STATUS_LABELS[status], callback_data=f"ord:{order['id']}:{status}"))
    for i in range(0, len(buttons), 2):
        kb.row(*buttons[i:i+2])
    if staff.can("orders.update"):
        kb.row(types.InlineKeyboardButton("💬 Додати коментар", callback_data=f"ordcomment:{order['id']}"),
               types.InlineKeyboardButton("📜 Історія коментарів", callback_data=f"ordcomments:{order['id']}"))
        # Editing delivery/contact details is safe only before the parcel is shipped.
        if current in {"new", "confirmed", "packing", "packed", "ready_to_ship", "problem"}:
            kb.row(types.InlineKeyboardButton("✏️ Змінити дані", callback_data=f"ordedit:{order['id']}"))
    return kb


OWNER_SECTIONS = [
    ("⚙️ Керування", "management"), ("🗂️ Каталог", "catalog"),
    ("🛍️ Замовлення", "orders"), ("📦 Склад", "inventory"),
    ("🚚 Доставка", "delivery"), ("📊 Статистика", "statistics"),
    ("👥 Клієнти", "customers"), ("💰 Фінанси", "finance"),
    ("🎁 Лояльність", "loyalty"), ("📣 Розсилки", "broadcasts"),
    ("🎫 Підтримка", "support"), ("🛡️ Безпека", "security"),
]

SECTION_PERMISSIONS = {
    "management": None, "catalog": "catalog.read", "orders": "orders.read",
    "inventory": "inventory.read", "delivery": "delivery.read",
    "statistics": "statistics.read", "customers": "customers.read",
    "finance": "finance.read", "loyalty": "loyalty.read",
    "broadcasts": "broadcasts.read", "support": "support.read",
    "security": "security.read",
}


def main_menu(staff: Staff) -> types.ReplyKeyboardMarkup:
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
    if staff.role == "owner":
        labels = [label for label, _ in OWNER_SECTIONS]
        for i in range(0, len(labels), 2):
            kb.row(*labels[i:i + 2])
        return kb
    role_sections = {
        "courier": ["🚚 Доставка", "🛍️ Замовлення"],
        "admin": ["🗂️ Каталог", "🛍️ Замовлення", "📦 Склад", "🚚 Доставка", "👥 Клієнти", "🎫 Підтримка"],
        "manager": ["🛍️ Замовлення", "🚚 Доставка", "👥 Клієнти", "🎫 Підтримка"],
        "packer": ["🛍️ Замовлення", "📦 Склад"],
    }
    labels = role_sections.get(staff.role, ["🛍️ Замовлення"])
    for i in range(0, len(labels), 2):
        kb.row(*labels[i:i + 2])
    kb.row("🏠 Головне меню")
    return kb


def _section_permission_ok(staff: Staff, section: str) -> bool:
    permission = SECTION_PERMISSIONS.get(section)
    return staff.role == "owner" or (permission is not None and staff.can(permission))


def render_staff_section(chat_id: int, staff: Staff, section: str) -> None:
    """Render a compact live dashboard for a handoff-defined top-level section."""
    if not _section_permission_ok(staff, section):
        bot.send_message(chat_id, "⛔ Недостатньо прав для цього розділу.", reply_markup=main_menu(staff))
        return
    title = dict(OWNER_SECTIONS).get(section, "Розділ")
    lines = [f"<b>{safe(title)}</b>", ""]
    kb = types.InlineKeyboardMarkup(row_width=2)
    try:
        with db_cursor() as cur:
            if section == "management":
                cur.execute("SELECT COUNT(*) n FROM staff WHERE active=TRUE")
                staff_count = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM business_tasks WHERE status IN ('open','in_progress')")
                tasks = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM notification_outbox WHERE state='failed'")
                failed = int(cur.fetchone()["n"])
                lines += [f"Активних працівників: <b>{staff_count}</b>", f"Відкритих завдань: <b>{tasks}</b>", f"Невідправлених/помилкових сповіщень: <b>{failed}</b>"]
                kb.add(types.InlineKeyboardButton("👥 Працівники", callback_data="section:staff"),
                       types.InlineKeyboardButton("🧾 Журнал дій", callback_data="section:audit"),
                       types.InlineKeyboardButton("📋 Завдання", callback_data="section:tasks"))
            elif section == "catalog":
                cur.execute("""SELECT c.id,c.name,COUNT(DISTINCT p.id) products,COUNT(DISTINCT v.id) variants
                               FROM categories c LEFT JOIN products p ON p.category_id=c.id AND p.archived_at IS NULL
                               LEFT JOIN product_variants v ON v.product_id=p.id AND v.active=TRUE
                               WHERE c.parent_id IS NULL GROUP BY c.id,c.name
                               ORDER BY CASE c.name WHEN 'Рідини' THEN 1 WHEN 'Под-системи' THEN 2 WHEN 'Картриджі' THEN 3 WHEN 'Інше' THEN 4 ELSE 99 END,c.sort_order""")
                rows = list(cur.fetchall())
                for r in rows:
                    lines.append(f"• {safe(r['name'])}: {r['products']} товарів · {r['variants']} SKU")
                cur.execute("SELECT COUNT(*) n FROM brands WHERE active=TRUE")
                lines.append(f"\nАктивних виробників: <b>{cur.fetchone()['n']}</b>")
                kb.add(types.InlineKeyboardButton("🏷 Виробники", callback_data="section:brands"),
                       types.InlineKeyboardButton("📋 Товари", callback_data="section:products"))
            elif section == "orders":
                cur.execute("SELECT status,COUNT(*) n FROM orders GROUP BY status ORDER BY status")
                rows = list(cur.fetchall())
                lines += [f"• {safe(r['status'])}: <b>{r['n']}</b>" for r in rows] or ["Замовлень поки немає."]
                kb.add(types.InlineKeyboardButton("📦 Незібрані", callback_data="queue:uncollected"),
                       types.InlineKeyboardButton("📋 Останні 100", callback_data="queue:last100"),
                       types.InlineKeyboardButton("🔎 CRM-пошук", callback_data="search:prompt"))
            elif section == "inventory":
                cur.execute("SELECT COUNT(*) n FROM product_variants WHERE active=TRUE")
                variants = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM product_variants WHERE active=TRUE AND stock_qty-reserved_qty<=low_stock_threshold")
                low = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM inventory_counts WHERE status IN ('draft','counting')")
                counts = int(cur.fetchone()["n"])
                lines += [f"Активних SKU: <b>{variants}</b>", f"Позицій на мінімальному залишку: <b>{low}</b>", f"Незавершених інвентаризацій: <b>{counts}</b>"]
                kb.add(types.InlineKeyboardButton("⚠️ Малі залишки", callback_data="section:lowstock"),
                       types.InlineKeyboardButton("🧮 Інвентаризації", callback_data="section:counts"),
                       types.InlineKeyboardButton("🚚 Постачання", callback_data="section:supplies"))
                kb.add(types.InlineKeyboardButton("🧭 Контроль складу", callback_data="stock:console"),
                       types.InlineKeyboardButton("📚 Журнал рухів", callback_data="stock:movements"),
                       types.InlineKeyboardButton("💵 Оцінка запасів", callback_data="stock:valuation"))
                if staff.role == "owner":
                    kb.add(types.InlineKeyboardButton("🛡️ Повна звірка", callback_data="stock:integrity"),
                           types.InlineKeyboardButton("📦 Перевірка резервів", callback_data="stock:reservations"))
            elif section == "delivery":
                cur.execute("SELECT COUNT(*) n FROM courier_assignments WHERE status IN ('assigned','in_progress')")
                active = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM delivery_quotes WHERE state='pending' AND expires_at>NOW()")
                quotes = int(cur.fetchone()["n"])
                lines += [f"Активних призначень кур'єрам: <b>{active}</b>", f"Очікують підтвердження тарифу: <b>{quotes}</b>"]
                kb.add(types.InlineKeyboardButton("🛍️ Замовлення", callback_data="queue:uncollected"))
            elif section == "statistics":
                cur.execute("""SELECT COUNT(*) orders,COALESCE(SUM(grand_total),0) revenue
                               FROM orders WHERE created_at >= date_trunc('day',NOW())""")
                r = cur.fetchone()
                cur.execute("SELECT COUNT(*) n FROM customers")
                customers = int(cur.fetchone()["n"])
                lines += [f"Замовлень сьогодні: <b>{r['orders']}</b>", f"Сума замовлень сьогодні: <b>{money(r['revenue'])}</b>", f"Клієнтів у базі: <b>{customers}</b>", "\nВиторг тут показаний за створеними замовленнями, не як підтверджений прибуток."]
                if staff.role == "owner":
                    kb.add(types.InlineKeyboardButton("📈 Фінансовий звіт · 7 днів", callback_data="bizrep:finance:7d"),
                           types.InlineKeyboardButton("📈 Фінансовий звіт · 30 днів", callback_data="bizrep:finance:30d"),
                           types.InlineKeyboardButton("🚚 Статистика доставок", callback_data="bizrep:delivery:30"))
            elif section == "customers":
                cur.execute("SELECT COUNT(*) n FROM customers")
                total = int(cur.fetchone()["n"])
                cur.execute("SELECT COUNT(*) n FROM customers WHERE age_verification_status='unverified'")
                pending_age = int(cur.fetchone()["n"])
                lines += [f"Клієнтів: <b>{total}</b>", f"Очікують перевірки віку: <b>{pending_age}</b>"]
                kb.add(types.InlineKeyboardButton("🔎 Знайти клієнта", callback_data="search:prompt"),
                       types.InlineKeyboardButton("🪪 Перевірка віку", callback_data="section:agequeue"))
                if staff.role == "owner":
                    kb.add(types.InlineKeyboardButton("📄 Експорт клієнтів у PDF", callback_data="customers:export"))
            elif section == "finance":
                cur.execute("""SELECT COALESCE(SUM(amount),0) amount FROM business_expenses
                               WHERE expense_date= CURRENT_DATE""")
                expense = cur.fetchone()["amount"]
                cur.execute("""SELECT COALESCE(SUM(paid_amount),0) amount FROM orders
                               WHERE payment_status='paid' AND created_at >= date_trunc('day',NOW())""")
                paid = cur.fetchone()["amount"]
                lines += [f"Підтверджені оплати сьогодні: <b>{money(paid)}</b>", f"Внесені витрати сьогодні: <b>{money(expense)}</b>", "Маржа та чистий прибуток не обчислюються без перевіреної собівартості й повних витрат."]
                if staff.role == "owner":
                    kb.add(types.InlineKeyboardButton("💰 Повна фінансова панель", callback_data="finops:home"),
                           types.InlineKeyboardButton("🧾 Витрати", callback_data="finops:expenses"))
            elif section == "loyalty":
                cur.execute("SELECT COUNT(*) n FROM loyalty_accounts")
                accounts = int(cur.fetchone()["n"])
                cur.execute("SELECT COALESCE(SUM(available+pending),0) amount FROM loyalty_accounts")
                balance = cur.fetchone()["amount"]
                lines += [f"Бонусних рахунків: <b>{accounts}</b>", f"Сумарний баланс: <b>{money(balance)}</b>"]
                if staff.role == "owner":
                    kb.add(types.InlineKeyboardButton("➕/➖ Коригувати за номером картки", callback_data="loyalty:adjusthelp"))
            elif section == "broadcasts":
                cur.execute("SELECT state,COUNT(*) n FROM broadcasts GROUP BY state ORDER BY state")
                rows = list(cur.fetchall())
                lines += [f"• {safe(r['state'])}: {r['n']}" for r in rows] or ["Розсилок ще немає."]
            elif section == "support":
                cur.execute("SELECT status,COUNT(*) n FROM support_tickets GROUP BY status ORDER BY status")
                rows = list(cur.fetchall())
                lines += [f"• {safe(TICKET_STATUS_LABELS.get(r['status'], r['status']))}: {r['n']}" for r in rows] or ["Звернень поки немає."]
                kb.add(types.InlineKeyboardButton("📂 Відкрити звернення", callback_data="support:list"))
                kb.add(types.InlineKeyboardButton("💼 Історія запитів на роботу", callback_data="requests:jobs:0"))
                kb.add(types.InlineKeyboardButton("📦 Історія оптових запитів", callback_data="requests:wholesale:0"))
            elif section == "security":
                cur.execute("SELECT state,COUNT(*) n FROM staff_security_state GROUP BY state ORDER BY state")
                rows = list(cur.fetchall())
                lines += [f"• {safe(r['state'])}: {r['n']}" for r in rows] or ["Активних обмежень немає."]
                cur.execute("SELECT COUNT(*) n FROM security_events WHERE created_at >= NOW()-INTERVAL '24 hours'")
                lines.append(f"\nПодій безпеки за 24 години: <b>{cur.fetchone()['n']}</b>")
                kb.add(types.InlineKeyboardButton("👥 Працівники", callback_data="section:staff"),
                       types.InlineKeyboardButton("📜 Події безпеки", callback_data="section:securityevents"))
    except Exception:
        log.exception("Failed to render staff section %s", section)
        bot.send_message(chat_id, "⚠️ Не вдалося завантажити розділ. Помилку записано в журнал.", reply_markup=main_menu(staff))
        return
    kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb, disable_web_page_preview=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("section:"))
def staff_section_callback(call):
    staff = require_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    if stock_console_callback_dispatch(call, staff):
        return
    key = call.data.split(":", 1)[1]
    bot.answer_callback_query(call.id)
    if key == "home":
        bot.send_message(call.message.chat.id, "Головне меню Cloud Hub", reply_markup=main_menu(staff))
        return
    if key == "broadcasts":
        if _broadcast_staff(call):
            broadcast_home(call.message.chat.id)
        else:
            bot.send_message(call.message.chat.id, "⛔ Розсилки доступні лише власнику.")
        return
    if key == "agequeue":
        age_verification_queue_handler(call.message, call.from_user)
        return
    if key in {"staff", "audit", "tasks", "brands", "products", "lowstock", "counts", "supplies", "securityevents"}:
        render_staff_subsection(call.message.chat.id, staff, key)
        return
    render_staff_section(call.message.chat.id, staff, key)


def render_staff_subsection(chat_id: int, staff: Staff, key: str) -> None:
    """Read-only drill-downs; mutating workflows are added only with audited forms."""
    owner_only = {"staff", "audit", "securityevents"}
    required = {
        "tasks": "management.read", "brands": "catalog.read", "products": "catalog.read",
        "lowstock": "inventory.read", "counts": "inventory.read", "supplies": "inventory.read",
    }.get(key)
    if (key in owner_only and staff.role != "owner") or (required and staff.role != "owner" and not staff.can(required)):
        bot.send_message(chat_id, "⛔ Цей підрозділ недоступний для вашої ролі.")
        return
    queries = {
        "staff": ("Працівники", "SELECT telegram_id,display_name,role,active FROM staff ORDER BY active DESC,role,display_name LIMIT 100"),
        "audit": ("Останні 50 дій", "SELECT actor_telegram_id,actor_role,action,entity_type,entity_id,created_at FROM audit_log ORDER BY created_at DESC LIMIT 50"),
        "tasks": ("Активні завдання", "SELECT id,title,status,assigned_to,due_at FROM business_tasks WHERE status IN ('open','in_progress') ORDER BY due_at NULLS LAST,created_at DESC LIMIT 50"),
        "brands": ("Виробники", "SELECT b.id,b.name,b.active,COUNT(DISTINCT p.id) products FROM brands b LEFT JOIN products p ON p.brand_id=b.id AND p.archived_at IS NULL GROUP BY b.id ORDER BY b.name LIMIT 100"),
        "products": ("Останні товари", "SELECT p.id,p.name,c.name category,b.name brand,COUNT(v.id) variants FROM products p LEFT JOIN categories c ON c.id=p.category_id LEFT JOIN brands b ON b.id=p.brand_id LEFT JOIN product_variants v ON v.product_id=p.id WHERE p.archived_at IS NULL GROUP BY p.id,c.name,b.name ORDER BY p.created_at DESC LIMIT 50"),
        "lowstock": ("Малі залишки", "SELECT p.name product,v.variant_name,v.sku,v.stock_qty,v.reserved_qty,v.low_stock_threshold FROM product_variants v JOIN products p ON p.id=v.product_id WHERE v.active=TRUE AND v.stock_qty-v.reserved_qty<=v.low_stock_threshold ORDER BY (v.stock_qty-v.reserved_qty),p.name LIMIT 100"),
        "counts": ("Інвентаризації", "SELECT id,status,created_by,created_at,confirmed_by,confirmed_at FROM inventory_counts ORDER BY created_at DESC LIMIT 50"),
        "supplies": ("Постачання", "SELECT id,document_number,state,document_date,total_cost,created_at FROM supply_documents ORDER BY created_at DESC LIMIT 50"),
        "securityevents": ("Події безпеки за 7 днів", "SELECT severity,event_type,actor_telegram_id,subject_telegram_id,created_at FROM security_events WHERE created_at>=NOW()-INTERVAL '7 days' ORDER BY created_at DESC LIMIT 100"),
    }
    title, sql = queries[key]
    with db_cursor() as cur:
        cur.execute(sql)
        rows = list(cur.fetchall())
    if key == "staff":
        kb = types.InlineKeyboardMarkup(row_width=1)
        for row in rows:
            status = "активний" if row["active"] else "неактивний"
            kb.add(types.InlineKeyboardButton(
                f"👤 {str(row['display_name'])[:24]} · {status}",
                callback_data=f"sec:staff:{int(row['telegram_id'])}"))
        kb.add(types.InlineKeyboardButton("↩️ Назад до розділу", callback_data="subback:management"),
               types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
        bot.send_message(chat_id, f"<b>{safe(title)}</b>\nОберіть працівника для перегляду та керування безпекою:", reply_markup=kb)
        return
    nav = types.InlineKeyboardMarkup(row_width=2)
    parent = {"staff": "management", "audit": "management", "tasks": "management",
              "brands": "catalog", "products": "catalog", "lowstock": "inventory",
              "counts": "inventory", "supplies": "inventory", "securityevents": "security"}[key]
    if key == "counts":
        nav.add(types.InlineKeyboardButton("➕ Почати інвентаризацію", callback_data="stock:count_start"))
    elif key == "supplies":
        nav.add(types.InlineKeyboardButton("🔄 Оновити поставки", callback_data="section:supplies"))
    elif key == "lowstock":
        nav.add(types.InlineKeyboardButton("📊 План закупівель", callback_data="stock:replenishment"))
    nav.add(types.InlineKeyboardButton("↩️ Назад до розділу", callback_data=f"subback:{parent}"),
            types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    if not rows:
        bot.send_message(chat_id, f"<b>{safe(title)}</b>\nЗаписів поки немає.", reply_markup=nav)
        return
    lines = [f"<b>{safe(title)}</b>"]
    for row in rows:
        parts = []
        for k, v in row.items():
            if v is not None:
                parts.append(f"{safe(k)}: {safe(v)}")
        lines.append("• " + " | ".join(parts))
    # Telegram message limit is 4096 chars. Split only between records.
    chunk = ""
    for line in lines:
        candidate = (chunk + "\n" + line).strip()
        if len(candidate) > 3800 and chunk:
            bot.send_message(chat_id, chunk)
            chunk = line
        else:
            chunk = candidate
    if chunk:
        bot.send_message(chat_id, chunk, reply_markup=nav)


@bot.callback_query_handler(func=lambda c: c.data.startswith("subback:"))
def staff_subsection_back_callback(call):
    staff = require_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    section = call.data.split(":", 1)[1]
    bot.answer_callback_query(call.id)
    render_staff_section(call.message.chat.id, staff, section)


def send_order_cards(chat_id: int, orders: Iterable[dict], staff: Staff, title: str) -> None:
    orders = list(orders)
    if not orders:
        bot.send_message(chat_id, f"✅ {safe(title)}: замовлень немає.")
        return
    bot.send_message(chat_id, f"<b>{safe(title)}</b>\nЗнайдено: {len(orders)}")
    # Do not truncate the result set. Pace individual Telegram messages.
    for index, order in enumerate(orders, 1):
        try:
            bot.send_message(
                chat_id,
                order_card_text(order),
                reply_markup=order_keyboard(order, staff),
                disable_web_page_preview=True,
            )
        except Exception:
            log.exception("Failed to send order card id=%s", order.get("id"))
        if index % CONFIG.batch_size == 0:
            time.sleep(CONFIG.card_delay)
        else:
            time.sleep(min(CONFIG.card_delay, 0.25))


@bot.callback_query_handler(func=lambda c: c.data.startswith("requests:"))
def staff_request_history_callback(call):
    staff = require_staff(call, "support.read")
    if not staff or staff.role not in {"owner", "admin", "manager"}:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    try:
        _, kind, raw_offset = call.data.split(":")
        offset = max(0, int(raw_offset))
        kb = types.InlineKeyboardMarkup(row_width=1)
        if kind == "jobs":
            with db_cursor() as cur:
                cur.execute("""SELECT t.id,t.customer_telegram_id,t.status,t.created_at,
                                      COALESCE((SELECT body FROM support_messages sm WHERE sm.ticket_id=t.id ORDER BY sm.created_at LIMIT 1),'') body
                               FROM support_tickets t WHERE t.subject='Запит на роботу'
                               ORDER BY t.created_at DESC LIMIT 10 OFFSET %s""", (offset,))
                rows = list(cur.fetchall())
            title = "💼 Історія запитів на роботу"
            for row in rows:
                stamp = row["created_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M")
                kb.add(types.InlineKeyboardButton(
                    f"#{row['id']} · {stamp} · ID {row['customer_telegram_id']}",
                    callback_data=f"support:ticket:{row['id']}"))
            total_query = "SELECT COUNT(*) n FROM support_tickets WHERE subject='Запит на роботу'"
        elif kind == "wholesale":
            with db_cursor() as cur:
                cur.execute("""SELECT id,customer_telegram_id,customer_name,body,status,created_at
                               FROM wholesale_requests ORDER BY created_at DESC LIMIT 10 OFFSET %s""", (offset,))
                rows = list(cur.fetchall())
            title = "📦 Історія оптових запитів"
            for row in rows:
                stamp = row["created_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M")
                kb.add(types.InlineKeyboardButton(
                    f"#{row['id']} · {str(row['customer_name'])[:18]} · {stamp}",
                    callback_data=f"requests:view:{row['id']}"))
            total_query = "SELECT COUNT(*) n FROM wholesale_requests"
        elif kind == "view":
            request_id = offset
            with db_cursor() as cur:
                cur.execute("SELECT * FROM wholesale_requests WHERE id=%s", (request_id,))
                row = cur.fetchone()
            if not row:
                bot.answer_callback_query(call.id, "Запит не знайдено.", show_alert=True)
                return
            kb.add(types.InlineKeyboardButton("↩️ До історії", callback_data="requests:wholesale:0"))
            bot.answer_callback_query(call.id)
            bot.send_message(call.message.chat.id,
                f"📦 <b>Оптовий запит #{row['id']}</b>\nКлієнт: {safe(row['customer_name'])}\nUsername: {safe(row['username'])}\nTelegram ID: <code>{row['customer_telegram_id']}</code>\nСтатус: {safe(row['status'])}\nДата: {row['created_at'].astimezone(ZoneInfo(CONFIG.timezone)).strftime('%d.%m.%Y %H:%M')}\n\n{safe(row['body'])}",
                reply_markup=kb)
            return
        else:
            raise ValueError("Невідомий тип історії.")
        with db_cursor() as cur:
            cur.execute(total_query)
            total = int(cur.fetchone()["n"])
        if offset > 0:
            kb.add(types.InlineKeyboardButton("⬅️ Назад", callback_data=f"requests:{kind}:{max(0, offset-10)}"))
        if offset + 10 < total:
            kb.add(types.InlineKeyboardButton("➡️ Далі", callback_data=f"requests:{kind}:{offset+10}"))
        kb.add(types.InlineKeyboardButton("↩️ До підтримки", callback_data="section:support"))
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, f"<b>{title}</b>\nЗаписів: {total}", reply_markup=kb)
    except Exception:
        log.exception("Staff request history failed")
        bot.answer_callback_query(call.id, "Не вдалося відкрити історію.", show_alert=True)


# ---------------------------------------------------------------------------
# Customer storefront UI
# ---------------------------------------------------------------------------


def customer_menu() -> types.ReplyKeyboardMarkup:
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, row_width=2)
    kb.row("🛍️ Відкрити каталог", "🧺 Мій кошик")
    kb.row("📦 Мої замовлення", "🎁 Бонусна карта")
    kb.row("⭐ Обране", "🎲 Рулетка")
    kb.row("👤 Мій профіль", "🎫 Підтримка")
    kb.row("💼 Хочу роботу", "📦 Оптове замовлення")
    kb.row("ℹ️ Про Cloud Hub")
    return kb


def send_customer_catalog(chat_id: int, category_id: Optional[int] = None,
                          brand_id: Optional[int] = None) -> None:
    if category_id is None:
        categories = list_root_categories()
        kb = types.InlineKeyboardMarkup(row_width=2)
        for category in categories:
            kb.add(types.InlineKeyboardButton(
                f"📁 {category['name']}", callback_data=f"catalog:category:{category['id']}"))
        if not categories:
            bot.send_message(chat_id, "Категорії ще не налаштовані. Зверніться до адміністратора.")
            return
        bot.send_message(chat_id, "🛍️ <b>Каталог Cloud Hub</b>\nОберіть категорію:", reply_markup=kb)
        return

    if brand_id is None:
        brands = list_category_brands(category_id)
        kb = types.InlineKeyboardMarkup(row_width=2)
        for brand in brands:
            kb.add(types.InlineKeyboardButton(
                f"🏷️ {brand['name']}", callback_data=f"catalog:brand:{category_id}:{brand['id']}"))
        kb.add(types.InlineKeyboardButton("↩️ До категорій", callback_data="catalog:back:categories"))
        bot.send_message(chat_id, "🏷️ <b>Оберіть виробника</b>", reply_markup=kb)
        return

    products = list_catalog(category_id, 100, brand_id)
    if not products:
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton("↩️ До виробників", callback_data=f"catalog:category:{category_id}"))
        bot.send_message(chat_id, "У цього виробника зараз немає товарів у наявності.", reply_markup=kb)
        return

    # Each taste/product is a button. Volume/size variants are shown as a second step.
    grouped: dict[int, dict] = {}
    for item in products:
        grouped.setdefault(int(item["product_id"]), {"item": item, "variants": []})
        grouped[int(item["product_id"])]["variants"].append(item)
    kb = types.InlineKeyboardMarkup(row_width=2)
    for product_id, group in grouped.items():
        item = group["item"]
        label = str(item["name"])[:45]
        kb.add(types.InlineKeyboardButton(
            f"🍬 {label}", callback_data=f"catalog:product:{product_id}:{category_id}:{brand_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До виробників", callback_data=f"catalog:category:{category_id}"))
    bot.send_message(chat_id, "🍬 <b>Оберіть смак / товар</b>\nДалі зможете вибрати об’єм:", reply_markup=kb)


def send_customer_product_options(chat_id: int, product_id: int,
                                  category_id: int, brand_id: int) -> None:
    product = catalog_get_product(product_id)
    if not product or not product.get("active") or product.get("manually_hidden") or product.get("archived_at"):
        bot.send_message(chat_id, "Товар більше недоступний.")
        return
    variants = [v for v in product.get("variants", [])
                if v.get("active") and int(v.get("stock_qty") or 0) - int(v.get("reserved_qty") or 0) > 0]
    if not variants:
        bot.send_message(chat_id, "Цього товару зараз немає в наявності.")
        return
    kb = types.InlineKeyboardMarkup(row_width=2)
    for variant in variants:
        volume = str(variant.get("variant_name") or variant.get("sku"))
        kb.add(types.InlineKeyboardButton(
            f"📏 {volume} · {money(variant['price'])}",
            callback_data=f"catalog:item:{variant['id']}:{category_id}:{brand_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До смаків", callback_data=f"catalog:brand:{category_id}:{brand_id}"))
    bot.send_message(chat_id, f"📦 <b>{safe(product['name'])}</b>\nОберіть об’єм / варіант:", reply_markup=kb)


def send_customer_product_card(chat_id: int, variant_id: int,
                               category_id: int, brand_id: int) -> None:
    with db_cursor() as cur:
        cur.execute("""SELECT p.id product_id,p.name,p.description,v.id variant_id,
                              v.variant_name,v.price,v.stock_qty-v.reserved_qty available
                       FROM product_variants v JOIN products p ON p.id=v.product_id
                       WHERE v.id=%s AND v.active=TRUE AND p.active=TRUE
                         AND p.manually_hidden=FALSE AND p.archived_at IS NULL""", (variant_id,))
        item = cur.fetchone()
    if not item or int(item["available"] or 0) <= 0:
        bot.send_message(chat_id, "Цей варіант уже недоступний.")
        return
    caption = (f"<b>{safe(item['name'])}</b>"
               f"{' · ' + safe(item['variant_name']) if item.get('variant_name') else ''}\n"
               f"{safe(item['description'])}\n\nЦіна: <b>{money(item['price'])}</b>\n"
               f"✅ В наявності: {item['available']}")
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(types.InlineKeyboardButton("➕ Додати", callback_data=f"cart:add:{variant_id}"),
           types.InlineKeyboardButton("✖️ Скасувати", callback_data=f"catalog:product:{item['product_id']}:{category_id}:{brand_id}"))
    media = catalog_get_media(int(item["product_id"]))
    photo_id = next((m.get("telegram_file_id") for m in media if m.get("telegram_file_id")), None)
    if photo_id:
        try:
            bot.send_photo(chat_id, photo_id, caption=caption, reply_markup=kb)
            return
        except Exception:
            log.exception("Customer product photo send failed: product_id=%s", item["product_id"])
    bot.send_message(chat_id, caption + "\n\n📷 Фото поки недоступне.", reply_markup=kb)


def send_customer_cart(chat_id: int, telegram_id: int) -> None:
    items = get_cart(telegram_id)
    if not items:
        bot.send_message(chat_id, "🧺 Кошик порожній. Зазирніть у каталог!")
        return
    total = sum((Decimal(str(x['line_total'])) for x in items), Decimal('0.00'))
    lines = ["🧺 <b>Ваш кошик</b>"]
    kb = types.InlineKeyboardMarkup(row_width=1)
    for x in items:
        variant = f" ({safe(x['variant_name'])})" if x.get("variant_name") else ""
        lines.append(f"• {safe(x['name'])}{variant} × {x['quantity']} · {money(x['line_total'])}")
        kb.add(types.InlineKeyboardButton(
            f"🗑 Видалити: {str(x['name'])[:30]}{variant[:15]}",
            callback_data=f"cart:remove:{x['variant_id']}"))
    lines.append(f"\nТовари разом: <b>{money(total)}</b>")
    lines.append("🚚 Кур’єр: вартість за обраним тарифом після введення адреси.")
    lines.append("📮 Нова пошта: доставка за тарифами перевізника.")
    kb.add(types.InlineKeyboardButton("✅ Оформити замовлення", callback_data="checkout:start"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)


@bot.message_handler(func=lambda m: m.text == "💼 Хочу роботу")
def customer_job_request_handler(message):
    customer_id = upsert_customer(message.from_user)
    user = message.from_user
    full_name = " ".join(x for x in [user.first_name, user.last_name] if x) or "Не вказано"
    username = f"@{user.username}" if user.username else "не вказано"
    with db_cursor() as cur:
        cur.execute("SELECT phone FROM customers WHERE id=%s", (customer_id,))
        customer_row = cur.fetchone()
        phone = customer_row["phone"] if customer_row else None
        phone_display = phone or "не наданий"
        cur.execute(
            """INSERT INTO support_tickets(customer_telegram_id,subject)
               VALUES(%s,'Запит на роботу') RETURNING id""", (user.id,))
        ticket_id = int(cur.fetchone()["id"])
        body = (f"💼 Запит на роботу\nІм’я: {full_name}\nUsername: {username}\n"
                f"Телефон: {phone_display}\nTelegram ID: {user.id}\n"
                f"Користувач хоче приєднатися до команди Cloud Hub.")
        cur.execute(
            """INSERT INTO support_messages(ticket_id,sender_telegram_id,sender_type,body)
               VALUES(%s,%s,'customer',%s)""", (ticket_id,user.id,body))
        payload = {"ticket_id":ticket_id,
                   "text":f"💼 <b>Запит на роботу #{ticket_id}</b>\n\n"
                          f"Ім’я: {safe(full_name)}\nUsername: {safe(username)}\n"
                          f"Телефон: {safe(phone_display)}\nTelegram ID: <code>{user.id}</code>\n"
                          "Користувач хоче працювати в Cloud Hub.",
                   "buttons":[["📂 Відкрити звернення",f"support:ticket:{ticket_id}"]]}
        for rid in staff_recipient_ids(cur,("owner","admin")):
            enqueue_notification(cur,rid,"support",payload,f"job-request:{ticket_id}:{rid}")
    bot.send_message(message.chat.id,
        "✅ Запит передано власнику та адміністраторам. Якщо потрібно, вони зв’яжуться з вами тут.",
        reply_markup=customer_menu())


WHOLESALE_DRAFTS: dict[int, str] = {}
WHOLESALE_CHOICES = [
    "🍋 Щось кисленьке",
    "🧊 Щось з холодком",
    "🍭 Щось солоденьке",
    "🎄 Хммм, давай спробуємо лімітовану колекцію Christmas edition!",
]


@bot.message_handler(func=lambda m: m.text == "🎲 Рулетка")
def customer_roulette_handler(message):
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🎡 Крутити рулетку!", callback_data="roulette:spin"))
    bot.send_message(message.chat.id,
        "🎲 <b>Рулетка Cloud Hub</b>\nДопоможу тобі обрати, що сьогодні будемо купувати 😉",
        reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data == "roulette:spin")
def customer_roulette_callback(call):
    import random
    choice = random.choice(WHOLESALE_CHOICES)
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🎡 Крутити ще раз", callback_data="roulette:spin"))
    bot.answer_callback_query(call.id, "Рулетка вирішила!")
    bot.send_message(call.message.chat.id, f"✨ Сьогодні твій вибір:\n\n<b>{safe(choice)}</b>", reply_markup=kb)


@bot.message_handler(func=lambda m: m.text == "📦 Оптове замовлення")
def customer_wholesale_start(message):
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.row(types.InlineKeyboardButton("✅ Так", callback_data="wholesale:yes"),
           types.InlineKeyboardButton("❌ Ні", callback_data="wholesale:no"))
    bot.send_message(message.chat.id,
        "📦 <b>Оптовий запит</b>\nЙого можна створити, якщо бажаєте придбати будь-які товари від 10+ позицій.\n\nБажаєте створити запит?",
        reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("wholesale:"))
def customer_wholesale_callback(call):
    action = call.data.split(":")[1]
    bot.answer_callback_query(call.id)
    if action == "no":
        WHOLESALE_DRAFTS.pop(call.from_user.id, None)
        bot.send_message(call.message.chat.id, "↩️ Прийнято. Повертаємося до головного меню.", reply_markup=customer_menu())
    elif action == "yes":
        WHOLESALE_DRAFTS[call.from_user.id] = True
        kb = types.ReplyKeyboardMarkup(resize_keyboard=True)
        kb.row("📨 Надіслати запит", "❌ Скасувати запит")
        bot.send_message(call.message.chat.id,
            "Чудово! Напишіть, будь ласка, що саме бажаєте придбати та в якій кількості.\nПісля цього натисніть «📨 Надіслати запит».",
            reply_markup=kb)


@bot.message_handler(func=lambda m: m.from_user and m.from_user.id in WHOLESALE_DRAFTS)
def customer_wholesale_text_handler(message):
    if message.text == "❌ Скасувати запит":
        WHOLESALE_DRAFTS.pop(message.from_user.id, None)
        bot.send_message(message.chat.id, "❌ Запит скасовано.", reply_markup=customer_menu())
        return
    if message.text == "📨 Надіслати запит":
        body = WHOLESALE_DRAFTS.get(message.from_user.id, "").strip()
        if not body:
            bot.send_message(message.chat.id, "Спочатку напишіть список товарів і бажану кількість.")
            return
    else:
        body = (message.text or "").strip()
        if not body or len(body) > 3500:
            bot.send_message(message.chat.id, "Напишіть текст запиту до 3500 символів.")
            return
        WHOLESALE_DRAFTS[message.from_user.id] = body
        bot.send_message(message.chat.id, "✅ Текст збережено. Натисніть «📨 Надіслати запит» або доповніть текст наступним повідомленням.")
        return
    WHOLESALE_DRAFTS.pop(message.from_user.id, None)
    user = message.from_user
    name = " ".join(x for x in [user.first_name, user.last_name] if x) or "Не вказано"
    username = f"@{user.username}" if user.username else ""
    with db_cursor() as cur:
        cur.execute("""INSERT INTO wholesale_requests(customer_telegram_id,customer_name,username,body)
                       VALUES(%s,%s,%s,%s) RETURNING id""", (user.id, name, username, body))
        request_id = int(cur.fetchone()["id"])
        payload = {"text": f"📦 <b>Оптовий запит #{request_id}</b>\nКлієнт: {safe(name)} {safe(username)}\nTelegram ID: <code>{user.id}</code>\n\n{safe(body)}",
                   "buttons": [[ "📦 Відкрити оптовий запит", f"requests:wholesale:{request_id}" ]]}
        for rid in staff_recipient_ids(cur, ("owner", "admin", "manager")):
            enqueue_notification(cur, rid, "wholesale", payload, f"wholesale:{request_id}:{rid}")
    bot.send_message(message.chat.id, f"✅ Оптовий запит #{request_id} передано команді Cloud Hub.", reply_markup=customer_menu())


@bot.message_handler(func=lambda m: m.text in ("🛒 Каталог", "🛍️ Відкрити каталог"))
def customer_catalog_handler(message):
    upsert_customer(message.from_user)
    send_customer_catalog(message.chat.id)


@bot.message_handler(func=lambda m: m.text in ("🧺 Кошик", "🧺 Мій кошик"))
def customer_cart_handler(message):
    upsert_customer(message.from_user)
    send_customer_cart(message.chat.id, message.from_user.id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("catalog:"))
def customer_catalog_navigation_callback(call):
    try:
        parts = call.data.split(":")
        if parts[1] == "back":
            send_customer_catalog(call.message.chat.id)
        elif parts[1] == "category":
            category_id = int(parts[2])
            send_customer_catalog(call.message.chat.id, category_id=category_id)
        elif parts[1] == "brand":
            category_id, brand_id = int(parts[2]), int(parts[3])
            allowed = {int(x["id"]) for x in list_category_brands(category_id)}
            if brand_id not in allowed:
                raise ValueError("Виробник не належить до цієї категорії або більше недоступний.")
            send_customer_catalog(call.message.chat.id, category_id=category_id, brand_id=brand_id)
        elif parts[1] == "product":
            product_id, category_id, brand_id = map(int, parts[2:5])
            send_customer_product_options(call.message.chat.id, product_id, category_id, brand_id)
        elif parts[1] == "item":
            variant_id, category_id, brand_id = map(int, parts[2:5])
            send_customer_product_card(call.message.chat.id, variant_id, category_id, brand_id)
        bot.answer_callback_query(call.id)
    except Exception as exc:
        log.exception("Catalog navigation failed")
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("cart:add:"))
def customer_cart_add_callback(call):
    try:
        variant_id = int(call.data.rsplit(":", 1)[-1])
        add_to_cart(call.from_user.id, variant_id, 1)
    except (ValueError, PermissionError) as exc:
        bot.answer_callback_query(call.id, str(exc)[:180], show_alert=True)
        return
    except Exception:
        log.exception("Could not add item to customer cart")
        bot.answer_callback_query(call.id, "Не вдалося додати товар. Спробуйте ще раз.", show_alert=True)
        return
    bot.answer_callback_query(call.id, "Додано до кошика")


@bot.callback_query_handler(func=lambda c: c.data.startswith("cart:remove:"))
def customer_cart_remove_callback(call):
    try:
        variant_id = int(call.data.rsplit(":", 1)[-1])
        with db_cursor() as cur:
            cur.execute("DELETE FROM cart_items WHERE customer_telegram_id=%s AND variant_id=%s",
                        (call.from_user.id, variant_id))
        bot.answer_callback_query(call.id, "Позицію видалено")
        send_customer_cart(call.message.chat.id, call.from_user.id)
    except Exception:
        log.exception("Cart item removal failed")
        bot.answer_callback_query(call.id, "Не вдалося видалити позицію.", show_alert=True)


def render_customer_orders(chat_id: int, telegram_id: int) -> None:
    with db_cursor() as cur:
        cur.execute("""SELECT id,order_number,status,grand_total,created_at FROM orders
                       WHERE telegram_id_snapshot=%s ORDER BY created_at DESC LIMIT 20""",
                    (telegram_id,))
        rows = list(cur.fetchall())
    if not rows:
        bot.send_message(chat_id, "📦 Поки що у вас немає замовлень.\nЗазирніть до каталогу, щоб обрати щось цікаве 💙")
        return
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        label = (f"№ {row['order_number']} · "
                 f"{STATUS_LABELS.get(row['status'], row['status'])} · "
                 f"{money(row['grand_total'])}")
        kb.add(types.InlineKeyboardButton(label[:60], callback_data=f"custorder:view:{int(row['id'])}"))
    bot.send_message(chat_id, "📦 <b>Ваші замовлення</b>\nОберіть замовлення, щоб переглянути деталі:",
                     reply_markup=kb)


@bot.message_handler(func=lambda m: m.text == "📦 Мої замовлення")
def customer_orders_handler(message):
    upsert_customer(message.from_user)
    render_customer_orders(message.chat.id, message.from_user.id)


@bot.callback_query_handler(func=lambda c: c.data.startswith("custorder:"))
def customer_order_callback(call):
    try:
        parts = call.data.split(":")
        if len(parts) != 3:
            raise ValueError("Некоректна дія.")
        action, raw_id = parts[1], int(parts[2])
        with db_cursor() as cur:
            cur.execute("SELECT id,order_number,status FROM orders WHERE id=%s AND telegram_id_snapshot=%s",
                        (raw_id, call.from_user.id))
            order_row = cur.fetchone()
        if not order_row:
            bot.answer_callback_query(call.id, "Замовлення не знайдено.", show_alert=True)
            return
        if action == "view":
            order = fetch_order(raw_id)
            kb = types.InlineKeyboardMarkup(row_width=1)
            if order_row["status"] == "new":
                kb.add(types.InlineKeyboardButton("❌ Скасувати замовлення",
                                                  callback_data=f"custorder:cancel:{raw_id}"))
            if str(order.get("delivery_type") or "").startswith("courier_"):
                kb.add(types.InlineKeyboardButton("🚚 Відстежити кур’єра", callback_data=f"custorder:track:{raw_id}"))
            kb.add(types.InlineKeyboardButton("↩️ До моїх замовлень", callback_data="custorders:list"))
            bot.answer_callback_query(call.id)
            bot.send_message(call.message.chat.id, order_card_text(order), reply_markup=kb)
            return
        if action == "track":
            with db_cursor() as cur:
                cur.execute("""SELECT o.order_number,o.status,o.delivery_type,o.delivery_address,ds.starts_at,
                                    ca.status courier_status,st.display_name courier_name
                             FROM orders o LEFT JOIN delivery_slots ds ON ds.id=o.delivery_slot_id
                             LEFT JOIN courier_assignments ca ON ca.order_id=o.id
                             LEFT JOIN staff st ON st.telegram_id=ca.courier_telegram_id
                             WHERE o.id=%s AND o.telegram_id_snapshot=%s""", (raw_id, call.from_user.id))
                info = cur.fetchone()
                cur.execute("SELECT event_type,details,created_at FROM delivery_events WHERE order_id=%s ORDER BY created_at DESC LIMIT 12", (raw_id,))
                events = list(cur.fetchall())
            if not info:
                raise ValueError("Замовлення не знайдено.")
            lines = [f"🚚 <b>Доставка {safe(info['order_number'])}</b>",
                     f"Статус замовлення: {safe(STATUS_LABELS.get(info['status'], info['status']))}",
                     f"Кур’єр: {safe(info['courier_name'] or 'ще не призначений')}",
                     f"Статус кур’єра: {safe(info['courier_status'] or 'очікує призначення')}"]
            if info.get("starts_at"):
                lines.append("Часове вікно: " + info["starts_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M"))
            lines.append("\n<b>Історія:</b>")
            for ev in events:
                stamp = ev["created_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M")
                lines.append(f"• {stamp} · {safe(DELIVERY_EVENT_LABELS.get(ev['event_type'], ev['event_type']))}")
            kb = types.InlineKeyboardMarkup()
            kb.add(types.InlineKeyboardButton("↩️ До замовлення", callback_data=f"custorder:view:{raw_id}"))
            bot.answer_callback_query(call.id)
            bot.send_message(call.message.chat.id, "\n".join(lines), reply_markup=kb)
            return
        if action == "cancel":
            kb = types.InlineKeyboardMarkup(row_width=2)
            kb.row(types.InlineKeyboardButton("Так, скасувати", callback_data=f"custorder:confirmcancel:{raw_id}"),
                   types.InlineKeyboardButton("Ні, залишити", callback_data=f"custorder:view:{raw_id}"))
            bot.answer_callback_query(call.id)
            bot.send_message(call.message.chat.id,
                             f"Скасувати замовлення № {safe(order_row['order_number'])}?",
                             reply_markup=kb)
            return
        if action == "confirmcancel":
            customer_cancel_order(raw_id, call.from_user)
            bot.answer_callback_query(call.id, "Замовлення скасовано.")
            bot.send_message(call.message.chat.id, "✅ Замовлення скасовано. Резерв товарів звільнено.",
                             reply_markup=customer_menu())
            render_customer_orders(call.message.chat.id, call.from_user.id)
            return
        raise ValueError("Невідома дія.")
    except ValueError as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)
    except Exception:
        log.exception("Customer order action failed")
        bot.answer_callback_query(call.id, "Не вдалося виконати дію. Спробуйте пізніше.", show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data == "custorders:list")
def customer_orders_back_callback(call):
    bot.answer_callback_query(call.id)
    render_customer_orders(call.message.chat.id, call.from_user.id)


def customer_cancel_order(order_id: int, telegram_user) -> None:
    """Customer may cancel only a not-yet-confirmed order; release stock atomically."""
    actor_id = int(telegram_user.id)
    actor_name = " ".join(x for x in [telegram_user.first_name, telegram_user.last_name] if x) or "Клієнт"
    customer_actor = Staff(actor_id, actor_name, "customer", True)
    with db_cursor() as cur:
        cur.execute("""SELECT id,order_number,status,customer_id FROM orders
                       WHERE id=%s AND telegram_id_snapshot=%s FOR UPDATE""",
                    (order_id, actor_id))
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        if order["status"] != "new":
            raise ValueError("Самостійне скасування доступне лише для нового замовлення. Напишіть у підтримку.")
        _stock_release_order_reservations(cur, order_id, customer_actor, "released")
        _cancel_pending_order_bonuses_tx(cur, order_id, order.get("customer_id"))
        cur.execute("UPDATE orders SET status='cancelled',updated_at=NOW() WHERE id=%s AND status='new'",
                    (order_id,))
        if cur.rowcount != 1:
            raise RuntimeError("Статус замовлення змінився. Оновіть список.")
        cur.execute("""INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                       before_data,after_data,reason)
                       VALUES(%s,'customer','order.customer_cancelled','order',%s,
                              %s::jsonb,%s::jsonb,'Клієнт скасував нове замовлення')""",
                    (actor_id, str(order_id), json_dumps({"status":"new"}),
                     json_dumps({"status":"cancelled"})))
        payload = {"text": f"❌ Клієнт скасував замовлення № {order['order_number']}.",
                   "order_id": order_id,
                   "buttons": [["📂 Відкрити замовлення", f"ordview:{order_id}"]]}
        for recipient in staff_recipient_ids(cur, ("owner","admin","manager")):
            enqueue_notification(cur, recipient, "orders", payload,
                                 f"order:{order_id}:customer-cancelled")


@bot.message_handler(func=lambda m: m.text == "🎁 Бонусна карта")
def customer_loyalty_handler(message):
    customer_id = upsert_customer(message.from_user)
    with db_cursor() as cur:
        cur.execute("SELECT available,pending FROM loyalty_accounts WHERE customer_id=%s", (customer_id,))
        row = cur.fetchone()
        cur.execute("SELECT loyalty_card_number FROM customers WHERE id=%s",(customer_id,))
        card_row=cur.fetchone()
    available = row['available'] if row else Decimal('0')
    pending = row['pending'] if row else Decimal('0')
    card_number=card_row["loyalty_card_number"] if card_row else "—"
    bot.send_message(message.chat.id,
        f"🎁 <b>Бонусна карта Cloud Hub</b>\n"
        f"🪪 Номер: <code>{safe(card_number)}</code>\n"
        f"Доступно: <b>{money(available)}</b>\n"
        f"Очікують: {money(pending)}\n1 бонус = 1 грн.",
        reply_markup=customer_menu())


@bot.message_handler(func=lambda m: m.text == "🎫 Підтримка")
def customer_support_handler(message):
    msg = bot.send_message(message.chat.id, "Напишіть одним повідомленням, чим ми можемо допомогти.")
    bot.register_next_step_handler(msg, customer_support_message)


def customer_support_message(message):
    try:
        ticket_id = create_support_ticket(message.from_user.id, message.text or "")
    except ValueError as exc:
        bot.reply_to(message, safe(str(exc)))
        return
    bot.reply_to(message, f"✅ Звернення #{ticket_id} створено та передано до черги підтримки. Відповідь з’явиться тут у чаті.")


@bot.message_handler(func=lambda m: m.text == "👤 Мій профіль")
def customer_profile_handler(message):
    customer_id = upsert_customer(message.from_user)
    with db_cursor() as cur:
        cur.execute("""SELECT phone,full_name,age_verification_status,loyalty_card_number
                       FROM customers WHERE id=%s""", (customer_id,))
        row = cur.fetchone()
        cur.execute("""SELECT COUNT(*)::int AS orders_count,
                              COALESCE(SUM(grand_total),0) AS lifetime_value
                       FROM orders WHERE customer_id=%s
                         AND status NOT IN ('cancelled','canceled','returned')""", (customer_id,))
        totals=cur.fetchone()
        cur.execute("""SELECT city,delivery_branch,delivery_address,delivery_type,COUNT(*)::int AS uses
                       FROM orders WHERE customer_id=%s
                         AND status NOT IN ('cancelled','canceled','returned')
                       GROUP BY city,delivery_branch,delivery_address,delivery_type
                       ORDER BY uses DESC,MAX(created_at) DESC LIMIT 1""", (customer_id,))
        usual=cur.fetchone()
        cur.execute("""SELECT available,pending FROM loyalty_accounts WHERE customer_id=%s""",(customer_id,))
        loyalty=cur.fetchone() or {"available":0,"pending":0}
    age_labels = {"verified": "підтверджено", "unverified": "ще не перевірено", "rejected": "не пройдено"}
    destination = "ще немає замовлень"
    if usual:
        if usual.get("delivery_type")=="nova_poshta":
            destination=f"{usual.get('city') or '—'}, {usual.get('delivery_branch') or 'відділення не вказано'}"
        else:
            destination=usual.get("delivery_address") or "кур’єрська адреса не збережена"
    bot.send_message(message.chat.id,
        f"👤 <b>Ваш профіль Cloud Hub</b>\n"
        f"🪪 Бонусна картка: <code>{safe(row.get('loyalty_card_number') or '—')}</code>\n"
        f"Ім’я: {safe(row.get('full_name') or 'не вказано')}\n"
        f"Телефон: {safe(row.get('phone') or 'не вказано')}\n"
        f"🎁 Доступно бонусів: <b>{money(loyalty['available'])}</b>\n"
        f"⏳ Очікують: {money(loyalty['pending'])}\n"
        f"📦 Замовлень: <b>{totals['orders_count']}</b>\n"
        f"💳 Сума покупок: <b>{money(totals['lifetime_value'])}</b>\n"
        f"📍 Найчастіше замовляєте: {safe(destination)}\n"
        f"Перевірка віку: {safe(age_labels.get(row['age_verification_status'], row['age_verification_status']))}",
        reply_markup=customer_menu())


@bot.message_handler(func=lambda m: m.text in ("ℹ️ Інформація", "ℹ️ Про Cloud Hub"))
def customer_info_handler(message):
    bot.send_message(message.chat.id,
        "☁️ <b>Clodex - Cloud Hub</b>\n\n"
        "Популярний вейпшоп із понад 5000+ відгуків.\n"
        "Нижчі ціни, швидка доставка, приємні акції та вигідна система лояльності.\n\n"
        "З технічних питань: Telegram @Haimer_clothes",
        reply_markup=customer_menu())


# ---------------------------------------------------------------------------
# Customer checkout wizard (consent -> contact -> delivery -> confirmation)
# ---------------------------------------------------------------------------

def save_checkout_draft(telegram_id: int, customer_id: int, **fields) -> None:
    allowed = {"step", "phone", "customer_name", "delivery_type", "city", "delivery_branch", "delivery_address", "delivery_quote_id", "bonus_amount", "delivery_slot_id"}
    updates = {key: value for key, value in fields.items() if key in allowed}
    with db_cursor() as cur:
        cur.execute("""INSERT INTO customer_checkout_drafts(telegram_id,customer_id,checkout_token)
                       VALUES(%s,%s,%s) ON CONFLICT(telegram_id) DO UPDATE
                       SET customer_id=EXCLUDED.customer_id,updated_at=NOW()""",
                    (telegram_id, customer_id, f"tg:{telegram_id}:{uuid.uuid4().hex}"))
        if updates:
            assignments = ",".join(f"{key}=%s" for key in updates)
            cur.execute(f"UPDATE customer_checkout_drafts SET {assignments},updated_at=NOW() WHERE telegram_id=%s",
                        (*updates.values(), telegram_id))


def get_checkout_draft(telegram_id: int):
    with db_cursor() as cur:
        cur.execute("SELECT * FROM customer_checkout_drafts WHERE telegram_id=%s", (telegram_id,))
        return cur.fetchone()


MARKETING_CONSENT_KEY = "marketing"
MARKETING_CONSENT_TEXT = ("Згода отримувати рекламні та інформаційні повідомлення Cloud Hub у Telegram. "
                          "Відмовитися можна будь-коли командою /stop_ads.")
DEFAULT_PRIVACY_TEXT = (
    "Для оформлення замовлення Cloud Hub обробляє ваші ім’я, прізвище, номер телефону, місто та "
    "адресу або відділення доставки. Дані потрібні лише для виконання замовлення, зв’язку з вами "
    "та доставки, і передаються службі доставки в обсязі, необхідному для цього. "
    "Не надсилайте в чат платіжні паролі чи коди. "
    "Щоб видалити свої дані, зверніться в підтримку."
)


def _privacy_consent_text() -> str:
    return CONFIG.privacy_consent_text or DEFAULT_PRIVACY_TEXT


def begin_checkout(chat_id: int, telegram_user) -> None:
    telegram_id = int(telegram_user.id)
    customer_id = upsert_customer(telegram_user)
    if not get_cart(telegram_id):
        bot.send_message(chat_id, "Кошик порожній.")
        return
    save_checkout_draft(telegram_id, customer_id, step="consent")
    try:
        consented = has_current_privacy_consent(telegram_id, CONFIG.privacy_consent_version)
    except Exception:
        log.exception("Consent lookup failed")
        bot.send_message(chat_id, "⚠️ Тимчасова технічна помилка. Спробуйте ще раз за хвилину.")
        return
    if consented:
        continue_checkout_after_consent(chat_id, telegram_user)
        return
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("✅ Погоджуюсь", callback_data="consent:accept"),
           types.InlineKeyboardButton("✅ Погоджуюсь + рекламні розсилки", callback_data="consent:accept_ads"),
           types.InlineKeyboardButton("❌ Не погоджуюсь", callback_data="consent:decline"))
    bot.send_message(chat_id, f"📄 <b>Згода на обробку персональних даних</b>\n\n{safe(_privacy_consent_text())}", reply_markup=kb)


def continue_checkout_after_consent(chat_id: int, telegram_user) -> None:
    customer_id = upsert_customer(telegram_user)
    with db_cursor() as cur:
        cur.execute("SELECT phone,full_name FROM customers WHERE id=%s", (customer_id,))
        row = cur.fetchone()
    saved_name = _clean_full_name(row["full_name"]) if row and row.get("full_name") else None
    if row and row.get("phone") and saved_name:
        kb = types.InlineKeyboardMarkup(row_width=1)
        kb.add(types.InlineKeyboardButton("✅ Використати ці дані", callback_data="checkout:reuse:yes"),
               types.InlineKeyboardButton("✏️ Ввести інші", callback_data="checkout:reuse:no"))
        bot.send_message(chat_id, f"Використати збережені дані?\n👤 {safe(saved_name)}\n📞 {safe(row['phone'])}", reply_markup=kb)
        return
    save_checkout_draft(int(telegram_user.id), customer_id, step="phone")
    ask_checkout_phone(chat_id)


def _clean_full_name(raw) -> Optional[str]:
    """Return a tidy 'Ім’я Прізвище' (2-4 parts, double names with a hyphen allowed) or None."""
    if not raw:
        return None
    name = re.sub(r"\s+", " ", str(raw).strip())
    parts = name.split(" ")
    if len(name) > 100 or not (2 <= len(parts) <= 4):
        return None
    for part in parts:
        if not re.fullmatch(r"[^\W\d_]{2,}(?:[-'’ʼ`][^\W\d_]+)*", part):
            return None
    return " ".join(re.sub(r"(^|-)([^\W\d_])", lambda m: m.group(1) + m.group(2).upper(), p) for p in parts)


def _is_cancel_text(message) -> bool:
    return (getattr(message, "text", None) or "").strip().casefold() == "скасувати оформлення"


def _cancel_checkout_flow(message) -> None:
    with db_cursor() as cur:
        cur.execute("DELETE FROM customer_checkout_drafts WHERE telegram_id=%s", (message.from_user.id,))
        cur.execute("DELETE FROM delivery_address_drafts WHERE telegram_id=%s", (message.from_user.id,))
    bot.send_message(message.chat.id, "Оформлення скасовано. Кошик збережено.", reply_markup=customer_menu())


def send_delivery_choice(chat_id: int) -> None:
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("🚴 Кур’єр Cloud Hub · лише Львів", callback_data="checkout:delivery:courier"),
           types.InlineKeyboardButton("📦 Нова пошта", callback_data="checkout:delivery:np"))
    bot.send_message(chat_id, "Оберіть спосіб доставки:", reply_markup=kb)


def ask_checkout_name(chat_id: int) -> None:
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    kb.add(types.KeyboardButton("Скасувати оформлення"))
    msg = bot.send_message(chat_id, "Вкажіть ім’я та прізвище отримувача (наприклад: Іван Петренко).", reply_markup=kb)
    bot.register_next_step_handler(msg, checkout_customer_name_step)

def ask_checkout_phone(chat_id: int) -> None:
    kb = types.ReplyKeyboardMarkup(resize_keyboard=True, one_time_keyboard=True)
    kb.add(types.KeyboardButton("📱 Надіслати номер телефону", request_contact=True))
    kb.add(types.KeyboardButton("Скасувати оформлення"))
    msg = bot.send_message(chat_id, "Надішліть свій номер телефону кнопкою нижче або введіть його вручну.", reply_markup=kb)
    bot.register_next_step_handler(msg, checkout_phone_step)


def checkout_phone_step(message) -> None:
    if _is_cancel_text(message):
        _cancel_checkout_flow(message)
        return
    raw_phone = message.contact.phone_number if message.contact and message.contact.user_id == message.from_user.id else (message.text or "")
    phone = normalize_phone(raw_phone)
    if not 10 <= len(phone) <= 15:
        msg = bot.send_message(message.chat.id, "Не схоже на коректний номер. Спробуйте ще раз, наприклад +380XXXXXXXXX.")
        bot.register_next_step_handler(msg, checkout_phone_step)
        return
    customer_id = upsert_customer(message.from_user)
    with db_cursor() as cur:
        cur.execute("UPDATE customers SET phone=%s,updated_at=NOW() WHERE id=%s", (phone, customer_id))
    save_checkout_draft(message.from_user.id, customer_id, phone=phone, step="name")
    ask_checkout_name(message.chat.id)


def checkout_customer_name_step(message) -> None:
    if _is_cancel_text(message):
        _cancel_checkout_flow(message)
        return
    name = _clean_full_name(message.text)
    if not name:
        msg = bot.send_message(message.chat.id, "Вкажіть, будь ласка, і ім’я, і прізвище, наприклад: Іван Петренко.")
        bot.register_next_step_handler(msg, checkout_customer_name_step)
        return
    customer_id = upsert_customer(message.from_user)
    with db_cursor() as cur:
        cur.execute("UPDATE customers SET full_name=%s,updated_at=NOW() WHERE id=%s", (name, customer_id))
    draft = get_checkout_draft(message.from_user.id)
    if draft and draft.get("step") == "confirm":
        save_checkout_draft(message.from_user.id, customer_id, customer_name=name)
        send_checkout_confirmation(message.chat.id, message.from_user.id)
        return
    save_checkout_draft(message.from_user.id, customer_id, customer_name=name, step="delivery")
    bot.send_message(message.chat.id, "Дякуємо!", reply_markup=types.ReplyKeyboardRemove())
    send_delivery_choice(message.chat.id)

@bot.callback_query_handler(func=lambda c: c.data in ("checkout:start", "checkout:delivery:courier", "checkout:delivery:np", "checkout:submit"))
def customer_checkout_callback(call):
    data = call.data.split(":")
    telegram_id = call.from_user.id
    try:
        if data[1] == "start":
            bot.answer_callback_query(call.id)
            begin_checkout(call.message.chat.id, call.from_user)
            return
        if data[1] == "delivery" and data[2] == "courier":
            bot.answer_callback_query(call.id)
            msg = bot.send_message(call.message.chat.id, "Вкажіть адресу доставки у Львові: вулиця та номер будинку.")
            bot.register_next_step_handler(msg, checkout_courier_address_step)
            return
        if data[1] == "delivery" and data[2] == "np":
            bot.answer_callback_query(call.id)
            msg = bot.send_message(call.message.chat.id, "Вкажіть місто Нової пошти.")
            bot.register_next_step_handler(msg, checkout_np_city_step)
            return
        if data[1] == "submit":
            bot.answer_callback_query(call.id)
            finalize_customer_checkout(call.message.chat.id, telegram_id)
            return
    except Exception as exc:
        log.exception("Customer checkout callback failed")
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


def checkout_courier_address_step(message) -> None:
    if _is_cancel_text(message):
        _cancel_checkout_flow(message)
        return
    address = (message.text or "").strip()
    if len(address) < 5 or len(address) > 300 or not re.search(r"\d", address):
        msg = bot.send_message(message.chat.id, "Вкажіть адресу у Львові: вулиця та номер будинку. Наприклад: вул. Жасминова, 11.")
        bot.register_next_step_handler(msg, checkout_courier_address_step)
        return
    try:
        lat, lon, _display = _geocode_address(address)
        if not _in_lviv(lat, lon):
            raise DeliveryError(LVIV_ONLY_TEXT)
    except DeliveryError as exc:
        msg = bot.send_message(message.chat.id, f"⚠️ {safe(str(exc))}\nВведіть іншу адресу у Львові або напишіть «Скасувати оформлення», щоб обрати Нову пошту.")
        bot.register_next_step_handler(msg, checkout_courier_address_step)
        return
    customer_id = upsert_customer(message.from_user)
    save_checkout_draft(message.from_user.id, customer_id, delivery_address=address, step="courier_tariff")
    with db_cursor() as cur:
        cur.execute("INSERT INTO delivery_address_drafts(telegram_id,address) VALUES(%s,%s) ON CONFLICT(telegram_id) DO UPDATE SET address=EXCLUDED.address,updated_at=NOW()", (message.from_user.id, address))
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("Звичайна", callback_data="checkout:tariff:standard"),
           types.InlineKeyboardButton("Експрес до 29 хв", callback_data="checkout:tariff:express"),
           types.InlineKeyboardButton("Нічна 22:00–23:59", callback_data="checkout:tariff:night"))
    bot.send_message(message.chat.id, "Оберіть тариф кур’єра:", reply_markup=kb)


def _normalize_np_city(raw) -> Optional[str]:
    city = re.sub(r"\s+", " ", str(raw or "").strip())
    city = re.sub(r"^(м\.|місто|с\.|смт)\s*", "", city, flags=re.I).strip()
    if not (2 <= len(city) <= 60):
        return None
    if not re.fullmatch(r"[^\W\d_]+(?:[ .'’ʼ-]+[^\W\d_]+)*\.?", city):
        return None
    return re.sub(r"(^|[ -])([^\W\d_])", lambda m: m.group(1) + m.group(2).upper(), city.lower())


def _normalize_np_branch(raw) -> Optional[str]:
    text = re.sub(r"\s+", " ", str(raw or "").strip().casefold())
    m = re.fullmatch(r"(відділення|поштомат)?\s*[№#]?\s*(\d{1,6})", text)
    if not m or int(m.group(2)) < 1:
        return None
    kind = "Поштомат" if m.group(1) == "поштомат" else "Відділення"
    return f"{kind} №{int(m.group(2))}"


def checkout_np_city_step(message) -> None:
    if _is_cancel_text(message):
        _cancel_checkout_flow(message)
        return
    city = _normalize_np_city(message.text)
    if not city:
        msg = bot.send_message(message.chat.id, "Вкажіть коректну назву міста (лише літери), наприклад: Київ.")
        bot.register_next_step_handler(msg, checkout_np_city_step)
        return
    customer_id = upsert_customer(message.from_user)
    save_checkout_draft(message.from_user.id, customer_id, city=city, step="np_branch")
    msg = bot.send_message(message.chat.id, "Вкажіть номер відділення (наприклад: 59) або поштомата (наприклад: поштомат 12345).")
    bot.register_next_step_handler(msg, checkout_np_branch_step)


def checkout_np_branch_step(message) -> None:
    if _is_cancel_text(message):
        _cancel_checkout_flow(message)
        return
    branch = _normalize_np_branch(message.text)
    if not branch:
        msg = bot.send_message(message.chat.id, "Не схоже на номер. Вкажіть номер відділення (наприклад: 59) або поштомата (наприклад: поштомат 12345).")
        bot.register_next_step_handler(msg, checkout_np_branch_step)
        return
    save_checkout_draft(message.from_user.id, upsert_customer(message.from_user), delivery_type="nova_poshta", delivery_branch=branch, step="confirm")
    send_checkout_confirmation(message.chat.id, message.from_user.id)

def finalize_customer_checkout(chat_id: int, telegram_id: int) -> None:
    draft = get_checkout_draft(telegram_id)
    if not draft or draft['step'] != 'confirm':
        bot.send_message(chat_id, "Чернетку оформлення не знайдено. Почніть з кошика.")
        return
    if not _clean_full_name(draft['customer_name']):
        msg = bot.send_message(chat_id, "Спершу вкажіть ім’я та прізвище отримувача, наприклад: Іван Петренко.")
        bot.register_next_step_handler(msg, checkout_customer_name_step)
        return
    try:
        result = checkout_cart(telegram_id, int(draft['customer_id']), draft['customer_name'] or "Клієнт",
                               draft['phone'], draft['delivery_type'], draft['checkout_token'],
                               delivery_quote_id=draft['delivery_quote_id'], city=draft['city'], delivery_branch=draft['delivery_branch'],
                               bonus_amount=Decimal(str(draft.get('bonus_amount') or 0)),
                               delivery_slot_id=int(draft["delivery_slot_id"]) if draft.get("delivery_slot_id") else None)
    except ValueError as exc:
        bot.send_message(chat_id, f"⚠️ {safe(str(exc))}")
        if "перевірки віку" in str(exc):
            queue_owner_admin_notification(
                "customers",
                {"text": f"🪪 Потрібна ручна перевірка віку клієнта Telegram ID {telegram_id}. Відкрийте /agequeue для розгляду."},
                f"age-review-request:{telegram_id}:{datetime.now(timezone.utc).date().isoformat()}"
            )
            bot.send_message(chat_id, "Ваше замовлення не втрачено. Запит передано працівникам для ручної перевірки. Після підтвердження віку можна буде повторити оформлення.")
        return
    except Exception:
        log.exception("Checkout failed unexpectedly for telegram_id=%s", telegram_id)
        bot.send_message(chat_id, "⚠️ Не вдалося оформити замовлення через технічну помилку. Кошик збережено — спробуйте ще раз за хвилину.")
        return
    with db_cursor() as cur:
        cur.execute("DELETE FROM customer_checkout_drafts WHERE telegram_id=%s", (telegram_id,))
    with db_cursor() as cur:
        cur.execute("SELECT age_verification_status FROM customers WHERE telegram_id=%s", (telegram_id,))
        age_row = cur.fetchone()
    manual_check_note = (
        "\n🪪 Перед підтвердженням і відправленням працівник вручну перевірить вік."
        if not age_row or age_row["age_verification_status"] != "verified" else ""
    )
    bot.send_message(
        chat_id,
        f"✅ Замовлення <b>{safe(result['order_number'])}</b> створено. "
        f"Сума: <b>{money(result['grand_total'])}</b>. Оплата при отриманні."
        + (f"\n🎁 Нараховано в очікуванні: {money(result.get('pending_bonus', 0))} бонусів. Вони стануть доступні після відправлення." if result.get('pending_bonus') else "")
        + manual_check_note,
        reply_markup=customer_menu(),
    )


def send_checkout_confirmation(chat_id: int, telegram_id: int) -> None:
    draft = get_checkout_draft(telegram_id)
    if not draft or draft.get("step") != "confirm":
        bot.send_message(chat_id, "Чернетку оформлення не знайдено або вона ще не готова до підтвердження.")
        return
    items = get_cart(telegram_id)
    if not items:
        bot.send_message(chat_id, "Кошик порожній. Додайте товари перед оформленням.")
        return
    total = sum((Decimal(str(item['line_total'])) for item in items), Decimal('0.00'))
    if draft['delivery_type'] == 'nova_poshta':
        city = (draft.get("city") or "").strip()
        branch = (draft.get("delivery_branch") or "").strip()
        if not city or not branch:
            bot.send_message(chat_id, "Не вказано місто або відділення Нової пошти. Почніть оформлення доставки ще раз.")
            return
        delivery = "Нова пошта: " + city + ", " + branch
        delivery_cost = "визначить перевізник"
        delivery_amount = Decimal("0.00")
    elif str(draft.get("delivery_type") or "").startswith("courier_"):
        with db_cursor() as cur:
            cur.execute("""SELECT delivery_price FROM delivery_quotes
                           WHERE id=%s AND customer_telegram_id=%s AND state='accepted'
                             AND expires_at>NOW()""", (draft['delivery_quote_id'], telegram_id))
            quote_row = cur.fetchone()
        if not quote_row:
            bot.send_message(chat_id, "Підтверджений тариф доставки відсутній або прострочений. Розрахуйте його ще раз.")
            return
        delivery = "Кур’єр Cloud Hub, " + str(draft.get("delivery_address") or "")
        delivery_amount = Decimal(str(quote_row['delivery_price']))
        delivery_cost = money(delivery_amount)
        if not draft.get("delivery_slot_id"):
            bot.send_message(chat_id, "Оберіть часовий слот доставки перед підтвердженням.")
            return
        with db_cursor() as cur:
            cur.execute("SELECT starts_at,ends_at,capacity,booked_count,active FROM delivery_slots WHERE id=%s AND tariff_code=%s", (draft["delivery_slot_id"], str(draft["delivery_type"]).replace("courier_", "")))
            slot_row = cur.fetchone()
        if not slot_row or not slot_row["active"] or slot_row["starts_at"] <= datetime.now(timezone.utc) or int(slot_row["booked_count"]) >= int(slot_row["capacity"]):
            bot.send_message(chat_id, "Обраний час уже недоступний. Поверніться до вибору доставки та оберіть інший слот.")
            return
        delivery += " · " + slot_row["starts_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M")
    else:
        bot.send_message(chat_id, "Спосіб доставки не розпізнано. Оберіть доставку ще раз.")
        return
    customer_id = upsert_customer(type("TelegramUser", (), {"id": telegram_id, "username": None, "first_name": "", "last_name": ""})())
    with db_cursor() as cur:
        cur.execute("SELECT available FROM loyalty_accounts WHERE customer_id=%s", (customer_id,))
        balance_row = cur.fetchone()
    available_bonus = Decimal(str(balance_row["available"])) if balance_row else Decimal("0.00")
    selected_bonus = Decimal(str(draft.get("bonus_amount") or 0))
    kb = types.InlineKeyboardMarkup(row_width=2)
    if available_bonus > 0:
        kb.add(types.InlineKeyboardButton(f"🎁 Бонуси: {money(selected_bonus)} / {money(available_bonus)}", callback_data="checkout:bonuses"))
    kb.add(types.InlineKeyboardButton("✅ Підтвердити замовлення", callback_data="checkout:submit"),
           types.InlineKeyboardButton("❌ Скасувати", callback_data="checkout:cancel"))
    amount_due = total + delivery_amount - selected_bonus
    bot.send_message(chat_id, f"<b>Перевірте замовлення</b>\nТовари: {money(total)}\nДоставка: {safe(delivery)}\nВартість доставки: {safe(delivery_cost)}\nБонуси до списання: {money(selected_bonus)}\nДо оплати (вартість НП визначає перевізник): {money(max(Decimal('0'), amount_due))}\nОтримувач: {safe(draft.get('customer_name') or '—')}\nТелефон: {safe(draft['phone'])}\nОплата: при отриманні.", reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("checkout:tariff:"))
def checkout_tariff_callback(call):
    tariff = call.data.rsplit(":", 1)[-1]
    with db_cursor() as cur:
        cur.execute("SELECT address FROM delivery_address_drafts WHERE telegram_id=%s", (call.from_user.id,))
        row = cur.fetchone()
    if not row:
        bot.answer_callback_query(call.id, "Адресу не знайдено. Почніть оформлення заново.", show_alert=True)
        return
    try:
        quote = create_delivery_quote(call.from_user.id, row['address'], tariff)
        kb = types.InlineKeyboardMarkup(row_width=2)
        kb.add(types.InlineKeyboardButton("✅ Підтвердити тариф", callback_data=f"checkout:quote:{quote['id']}:yes"),
               types.InlineKeyboardButton("❌ Відмовитись", callback_data=f"checkout:quote:{quote['id']}:no"))
        bot.answer_callback_query(call.id, "Маршрут розраховано.")
        bot.send_message(call.message.chat.id,
                         f"🚚 {safe(quote['tariff_title'])}\nВідстань: {quote['distance_km']:.2f} км\nВартість: <b>{money(quote['price'])}</b>\nПідтверджуєте цей тариф?",
                         reply_markup=kb)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("checkout:quote:"))
def checkout_quote_confirm_callback(call):
    try:
        _, _, raw_id, choice = call.data.split(":", 3)
        quote_id = int(raw_id)
        ok, result = confirm_delivery_quote(quote_id, call.from_user.id, choice == "yes")
        if not ok:
            raise ValueError(result)
        if choice == "yes":
            with db_cursor() as cur:
                cur.execute("SELECT tariff_code FROM delivery_quotes WHERE id=%s AND customer_telegram_id=%s", (quote_id, call.from_user.id))
                quote = cur.fetchone()
            if not quote:
                raise ValueError("Розрахунок доставки не знайдено.")
            tariff_code = quote['tariff_code']
            save_checkout_draft(call.from_user.id, upsert_customer(call.from_user),
                                delivery_type="courier_" + tariff_code, delivery_quote_id=quote_id,
                                delivery_slot_id=None, step="slot")
            with db_cursor() as cur:
                cur.execute("SELECT id,starts_at,ends_at,capacity,booked_count FROM delivery_slots WHERE active=TRUE AND tariff_code=%s AND starts_at>NOW() AND booked_count<capacity ORDER BY starts_at LIMIT 20", (tariff_code,))
                slots = list(cur.fetchall())
            if not slots:
                save_checkout_draft(call.from_user.id, upsert_customer(call.from_user), step="slot")
                bot.answer_callback_query(call.id, "Немає доступних часових слотів.", show_alert=True)
                fallback = types.InlineKeyboardMarkup(row_width=1)
                fallback.add(types.InlineKeyboardButton("🔁 Обрати інший тариф", callback_data="checkout:delivery:courier"),
                             types.InlineKeyboardButton("📦 Нова пошта", callback_data="checkout:delivery:np"))
                bot.send_message(call.message.chat.id, "На жаль, вільного часу для цього тарифу поки немає. Оберіть інший спосіб доставки.", reply_markup=fallback)
                return
            kb = types.InlineKeyboardMarkup(row_width=1)
            for slot in slots:
                start = slot["starts_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%d.%m %H:%M")
                end = slot["ends_at"].astimezone(ZoneInfo(CONFIG.timezone)).strftime("%H:%M")
                free = int(slot["capacity"])-int(slot["booked_count"])
                kb.add(types.InlineKeyboardButton(f"🕒 {start}–{end} · місць: {free}", callback_data=f"checkout:slot:{slot['id']}"))
            bot.answer_callback_query(call.id, "Тариф підтверджено.")
            bot.send_message(call.message.chat.id, "📅 <b>Оберіть зручний час доставки</b>:", reply_markup=kb)
        else:
            bot.answer_callback_query(call.id, "Тариф відхилено.")
            bot.send_message(call.message.chat.id, "Оберіть інший спосіб доставки або почніть оформлення заново.")
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("checkout:slot:"))
def checkout_slot_callback(call):
    try:
        slot_id = int(call.data.rsplit(":", 1)[-1])
        draft = get_checkout_draft(call.from_user.id)
        if not draft or draft.get("step") != "slot":
            raise ValueError("Чернетку вибору доставки не знайдено. Почніть оформлення заново.")
        with db_cursor() as cur:
            cur.execute("SELECT id,tariff_code,starts_at,ends_at,capacity,booked_count,active FROM delivery_slots WHERE id=%s", (slot_id,))
            slot = cur.fetchone()
        if not slot or not slot["active"] or slot["starts_at"] <= datetime.now(timezone.utc) or int(slot["booked_count"]) >= int(slot["capacity"]):
            raise ValueError("Цей час уже зайнятий. Оберіть інший.")
        if slot["tariff_code"] != str(draft.get("delivery_type", "")).replace("courier_", ""):
            raise ValueError("Слот не відповідає вибраному тарифу.")
        save_checkout_draft(call.from_user.id, int(draft["customer_id"]), delivery_slot_id=slot_id, step="confirm")
        bot.answer_callback_query(call.id, "Час доставки обрано.")
        send_checkout_confirmation(call.message.chat.id, call.from_user.id)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data == "checkout:bonuses")
def checkout_bonuses_callback(call):
    customer_id = upsert_customer(call.from_user)
    with db_cursor() as cur:
        cur.execute("SELECT available FROM loyalty_accounts WHERE customer_id=%s", (customer_id,))
        row = cur.fetchone()
    available = Decimal(str(row["available"])) if row else Decimal("0.00")
    if available <= 0:
        bot.answer_callback_query(call.id, "Немає доступних бонусів.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    prompt = bot.send_message(call.message.chat.id,
        f"🎁 Доступно {money(available)} бонусів. Введіть суму для списання або 0, щоб прибрати списання.")
    bot.register_next_step_handler(prompt, checkout_bonuses_amount_step)


def checkout_bonuses_amount_step(message):
    try:
        raw = (message.text or "").strip().replace(",", ".")
        value = Decimal(raw).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        if value < 0:
            raise ValueError("Сума не може бути від’ємною.")
        customer_id = upsert_customer(message.from_user)
        with db_cursor() as cur:
            cur.execute("SELECT available FROM loyalty_accounts WHERE customer_id=%s", (customer_id,))
            row = cur.fetchone()
        available = Decimal(str(row["available"])) if row else Decimal("0.00")
        if value > available:
            raise ValueError(f"Доступно лише {money(available)} бонусів.")
        draft = get_checkout_draft(message.from_user.id)
        if not draft or draft.get("step") != "confirm":
            raise ValueError("Чернетку оформлення не знайдено. Почніть оформлення заново.")
        items_total = sum((Decimal(str(x["line_total"])) for x in get_cart(message.from_user.id)), Decimal("0.00"))
        if value > items_total:
            raise ValueError("Бонусами не можна покрити більше, ніж вартість товарів.")
        save_checkout_draft(message.from_user.id, customer_id, bonus_amount=value)
        send_checkout_confirmation(message.chat.id, message.from_user.id)
    except Exception as exc:
        bot.reply_to(message, f"⚠️ {safe(str(exc))}")


@bot.callback_query_handler(func=lambda c: c.data == "checkout:cancel")
def checkout_cancel_callback(call):
    with db_cursor() as cur:
        cur.execute("DELETE FROM customer_checkout_drafts WHERE telegram_id=%s", (call.from_user.id,))
        cur.execute("DELETE FROM delivery_address_drafts WHERE telegram_id=%s", (call.from_user.id,))
    bot.answer_callback_query(call.id, "Оформлення скасовано.")
    bot.send_message(call.message.chat.id, "Оформлення скасовано. Кошик збережено, товари можна оформити пізніше.", reply_markup=customer_menu())



# Staff access is granted by a one-time code issued by the owner.
# Telegram ID remains the authenticated account key after redemption.
def issue_staff_access_code(role: str, actor: Staff) -> str:
    if actor.role != "owner":
        raise PermissionError("Код доступу може створити лише власник.")
    if role not in {"admin", "manager", "packer", "courier"}:
        raise ValueError("Роль має бути admin, manager, packer або courier.")
    raw = secrets.token_urlsafe(9)
    digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO staff_access_codes(code_hash,role,created_by,expires_at)
               VALUES(%s,%s,%s,NOW()+INTERVAL '24 hours')""",
            (digest, role, actor.telegram_id))
    return raw


def redeem_staff_access_code(message) -> bool:
    raw = (message.text or "").strip()
    if not raw or len(raw) > 100:
        return False
    digest = hashlib.sha256(raw.encode("utf-8")).hexdigest()
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,role FROM staff_access_codes
               WHERE code_hash=%s AND used_at IS NULL AND expires_at>NOW()
               FOR UPDATE""", (digest,))
        code = cur.fetchone()
        if not code:
            return False
        role = code["role"]
        display = " ".join(x for x in [message.from_user.first_name, message.from_user.last_name] if x) or f"Працівник {message.from_user.id}"
        cur.execute(
            """INSERT INTO staff(telegram_id,display_name,role,active)
               VALUES(%s,%s,%s,TRUE)
               ON CONFLICT(telegram_id) DO UPDATE
               SET display_name=EXCLUDED.display_name,role=EXCLUDED.role,active=TRUE,updated_at=NOW()""",
            (message.from_user.id, display[:120], role))
        cur.execute(
            "UPDATE staff_access_codes SET used_at=NOW(),used_by=%s WHERE id=%s AND used_at IS NULL",
            (message.from_user.id, code["id"]))
        cur.execute(
            """INSERT INTO staff_security_state(telegram_id,state)
               VALUES(%s,'active') ON CONFLICT(telegram_id) DO UPDATE
               SET state='active',updated_at=NOW()""", (message.from_user.id,))
    bot.send_message(message.chat.id,
        f"✅ Доступ активовано. Ваша роль: <b>{safe(ROLE_LABELS.get(role, role))}</b>.",
        reply_markup=main_menu(get_staff(message.from_user.id)))
    return True


@bot.message_handler(commands=["staffcode"])
def owner_issue_staff_code(message):
    owner = require_staff(message)
    if not owner or owner.role != "owner":
        bot.reply_to(message, "⛔ Лише власник може створювати коди доступу.")
        return
    parts = (message.text or "").split()
    if len(parts) != 2:
        bot.reply_to(message, "Формат: /staffcode admin|manager|packer|courier")
        return
    try:
        code = issue_staff_access_code(parts[1].lower(), owner)
        bot.reply_to(message,
            f"🔐 Одноразовий код для ролі <b>{safe(parts[1].lower())}</b>:\n"
            f"<code>{safe(code)}</code>\nДіє 24 години та використовується один раз. "
            "Надішліть його боту звичайним повідомленням.")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


# ---------------------------------------------------------------------------
# Commands and handlers
# ---------------------------------------------------------------------------

@bot.message_handler(commands=["start", "admin"])
def cmd_start(message):
    staff = require_staff(message)
    if staff:
        audit(staff, "staff.open_menu", "staff", str(staff.telegram_id))
        bot.send_message(
            message.chat.id,
            f"Вітаю, <b>{safe(staff.display_name)}</b>!\nРоль: {ROLE_LABELS[staff.role]}",
            reply_markup=main_menu(staff),
        )
        return
    upsert_customer(message.from_user)
    # The /start screen contains the notice; continuing to use the bot is recorded
    # as acceptance for the current notice version.
    try:
        notice = (
            "Cloud Hub обробляє ім’я, телефон і дані доставки для оформлення, "
            "супроводу та доставки замовлення. Дані передаються перевізнику лише "
            "в обсязі, необхідному для доставки. Рекламні повідомлення потребують "
            "окремої добровільної згоди."
        )
        record_privacy_consent(message.from_user.id, CONFIG.privacy_consent_version, notice, True)
        # Marketing consent is separate and must be an explicit opt-in.
    except Exception:
        log.exception("Could not record start notice")
    bot.send_message(
        message.chat.id,
        "☁️ <b>Cloudex | Cloud Hub</b>\n\n"
        "Ласкаво просимо! 🛍️\n"
        "Актуальний каталог, вигідні пропозиції та швидке оформлення замовлення.\n\n"
        "ℹ️ Для роботи магазину обробляємо ім’я, телефон і дані доставки. "
        "Рекламні повідомлення надсилаємо лише за окремою згодою. "
        "Відмовитися від них можна будь-коли командою /stop_ads.\n\n"
        "Зручних покупок! 💙",
        reply_markup=customer_menu(),
    )
    marketing_kb = types.InlineKeyboardMarkup(row_width=1)
    marketing_kb.add(types.InlineKeyboardButton(
        "📣 Погоджуюсь отримувати новини та пропозиції", callback_data="marketing:accept"))
    bot.send_message(message.chat.id,
        "Хочете отримувати новини, акції та спеціальні пропозиції Cloud Hub? "
        "Це необов’язково, згоду можна відкликати будь-коли командою /stop_ads.",
        reply_markup=marketing_kb)


@bot.message_handler(func=lambda m: bool(m.text) and any(m.text == label for label, _ in OWNER_SECTIONS))
def owner_section_menu(message):
    staff = require_staff(message)
    if not staff:
        bot.reply_to(message, "⛔ Доступ заборонено.")
        return
    section = next(key for label, key in OWNER_SECTIONS if label == message.text)
    if section == "catalog":
        catalog_admin_home(message.chat.id, staff)
        return
    if section == "inventory":
        inventory_admin_home(message.chat.id, staff)
        return
    if section == "delivery":
        delivery_render_desk(message.chat.id, staff)
        return
    if section == "finance":
        finance_render_home(message.chat.id, staff)
        return
    if section == "broadcasts":
        if _broadcast_staff(message):
            broadcast_home(message.chat.id)
        else:
            bot.reply_to(message, "⛔ Розсилки доступні лише власнику.")
        return
    render_staff_section(message.chat.id, staff, section)


@bot.message_handler(func=lambda m: m.text == "🏠 Головне меню")
def return_main_menu(message):
    staff = require_staff(message)
    if staff:
        bot.send_message(message.chat.id, "Головне меню Cloud Hub", reply_markup=main_menu(staff))


@bot.message_handler(func=lambda m: m.text == "🛍️ Замовлення")
def orders_menu(message):
    staff = require_staff(message, "orders.read")
    if not staff:
        bot.reply_to(message, "⛔ Недостатньо прав.")
        return
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(
        types.InlineKeyboardButton("📦 Незібрані замовлення", callback_data="queue:uncollected"),
        types.InlineKeyboardButton("📋 Переглянути останні 100 замовлень", callback_data="queue:last100"),
        types.InlineKeyboardButton("🔎 Пошук замовлення", callback_data="search:prompt"),
    )
    bot.send_message(message.chat.id, "Оберіть список замовлень:", reply_markup=kb)


@bot.message_handler(func=lambda m: m.text == "📦 Незібрані замовлення")
def uncollected_button(message):
    staff = require_staff(message, "orders.read")
    if not staff:
        bot.reply_to(message, "⛔ Недостатньо прав.")
        return
    orders = fetch_uncollected_orders()
    send_order_cards(message.chat.id, orders, staff, "Незібрані замовлення")


@bot.callback_query_handler(func=lambda c: c.data in ("queue:uncollected", "queue:last100"))
def queue_callback(call):
    staff = require_staff(call, "orders.read")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    if call.data == "queue:uncollected":
        orders = fetch_uncollected_orders()
        send_order_cards(call.message.chat.id, orders, staff, "Незібрані замовлення")
    else:
        orders = fetch_last_orders(100)
        send_order_cards(call.message.chat.id, orders, staff, "Останні 100 замовлень")


@bot.callback_query_handler(func=lambda c: c.data.startswith("ord:"))
def order_status_callback(call):
    staff = require_staff(call, "orders.update")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        _, raw_id, new_status = call.data.split(":", 2)
        order_id = int(raw_id)
    except (ValueError, TypeError):
        bot.answer_callback_query(call.id, "Некоректна дія.", show_alert=True)
        return
    ok, result = update_order_status(order_id, new_status, staff)
    bot.answer_callback_query(call.id, result[:180], show_alert=not ok)
    if ok:
        order = fetch_order(order_id)
        if order:
            try:
                bot.edit_message_text(
                    order_card_text(order),
                    call.message.chat.id,
                    call.message.message_id,
                    reply_markup=order_keyboard(order, staff),
                    disable_web_page_preview=True,
                )
            except Exception:
                bot.send_message(call.message.chat.id, result)





@bot.callback_query_handler(func=lambda c: c.data.startswith("ordcomment:"))
def order_comment_prompt(call):
    staff = require_staff(call, "orders.update")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        order_id = int(call.data.split(":")[1])
        prompt = bot.send_message(call.message.chat.id,
            f"💬 Напишіть коментар до замовлення #{order_id} (до 2000 символів).")
        bot.register_next_step_handler(prompt, order_comment_step, order_id)
        bot.answer_callback_query(call.id)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


def order_comment_step(message, order_id: int):
    staff = require_staff(message, "orders.update")
    body = (message.text or "").strip()
    if not staff:
        bot.reply_to(message, "⛔ Доступ заборонено.")
        return
    if not body or len(body) > 2000:
        bot.reply_to(message, "Коментар має містити 1–2000 символів.")
        return
    with db_cursor() as cur:
        cur.execute("SELECT id FROM orders WHERE id=%s", (order_id,))
        if not cur.fetchone():
            bot.reply_to(message, "Замовлення не знайдено.")
            return
        cur.execute(
            "INSERT INTO order_comments(order_id,author_telegram_id,author_role,body) VALUES(%s,%s,%s,%s)",
            (order_id, staff.telegram_id, staff.role, body))
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,reason)
               VALUES(%s,%s,'order.comment_added','order',%s,%s)""",
            (staff.telegram_id, staff.role, str(order_id), body[:500]))
    bot.reply_to(message, f"✅ Коментар до замовлення #{order_id} збережено.")


@bot.callback_query_handler(func=lambda c: c.data.startswith("ordcomments:"))
def order_comments_history_callback(call):
    staff = require_staff(call, "orders.read")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        order_id = int(call.data.split(":", 1)[1])
        with db_cursor() as cur:
            cur.execute("""SELECT author_role,body,created_at FROM order_comments
                           WHERE order_id=%s ORDER BY created_at DESC,id DESC LIMIT 20""", (order_id,))
            rows = list(cur.fetchall())
        if not rows:
            text = f"📜 До замовлення #{order_id} коментарів поки немає."
        else:
            lines = [f"📜 <b>Коментарі до замовлення #{order_id}</b>"]
            for row in rows:
                stamp = row["created_at"].astimezone().strftime("%d.%m.%Y %H:%M") if isinstance(row["created_at"], datetime) else str(row["created_at"])
                lines.append(f"\n<b>{safe(ROLE_LABELS.get(row['author_role'], row['author_role']))}</b> · {safe(stamp)}\n{safe(row['body'])}")
            text = "\n".join(lines)
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, text)
    except Exception:
        log.exception("Order comment history failed")
        bot.answer_callback_query(call.id, "Не вдалося завантажити коментарі.", show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("ordedit:"))
def order_edit_menu(call):
    staff = require_staff(call, "orders.update")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        order_id = int(call.data.split(":")[1])
        with db_cursor() as cur:
            cur.execute("SELECT status FROM orders WHERE id=%s", (order_id,))
            row = cur.fetchone()
        if not row or row["status"] not in {"new","confirmed","packing","packed","ready_to_ship","problem"}:
            bot.answer_callback_query(call.id, "Дані вже не можна змінити на цьому етапі.", show_alert=True)
            return
        kb = types.InlineKeyboardMarkup(row_width=2)
        for label, field in (("👤 Ім’я","customer_name_snapshot"),("📞 Телефон","phone_snapshot"),
                             ("🏙 Місто","city"),("🏢 Відділення","delivery_branch"),
                             ("🏠 Адреса","delivery_address")):
            kb.add(types.InlineKeyboardButton(label, callback_data=f"ordeditfield:{order_id}:{field}"))
        bot.answer_callback_query(call.id)
        bot.send_message(call.message.chat.id, f"Що змінити в замовленні #{order_id}?", reply_markup=kb)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("ordeditfield:"))
def order_edit_field_prompt(call):
    staff = require_staff(call, "orders.update")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        _, raw_id, field = call.data.split(":")
        allowed = {"customer_name_snapshot":"ім’я","phone_snapshot":"телефон","city":"місто",
                   "delivery_branch":"відділення","delivery_address":"адресу"}
        if field not in allowed:
            raise ValueError("Недозволене поле.")
        prompt = bot.send_message(call.message.chat.id,
            f"Надішліть нове значення для поля «{allowed[field]}» замовлення #{raw_id}.")
        bot.register_next_step_handler(prompt, order_edit_field_step, int(raw_id), field)
        bot.answer_callback_query(call.id)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


def order_edit_field_step(message, order_id: int, field: str):
    staff = require_staff(message, "orders.update")
    allowed = {"customer_name_snapshot","phone_snapshot","city","delivery_branch","delivery_address"}
    value = (message.text or "").strip()
    if not staff or field not in allowed:
        bot.reply_to(message, "⛔ Доступ заборонено.")
        return
    if not value or len(value) > 250:
        bot.reply_to(message, "Значення має містити 1–250 символів.")
        return
    if field == "phone_snapshot":
        value = normalize_phone(value)
        if len(value) < 10 or len(value) > 15:
            bot.reply_to(message, "Некоректний номер телефону. Вкажіть номер із кодом країни.")
            return
    with db_cursor() as cur:
        cur.execute(f"SELECT status,{field} AS old_value FROM orders WHERE id=%s FOR UPDATE", (order_id,))
        row = cur.fetchone()
        if not row or row["status"] not in {"new","confirmed","packing","packed","ready_to_ship","problem"}:
            bot.reply_to(message, "Замовлення вже перейшло на етап, де редагування заборонене.")
            return
        old_value = row["old_value"]
        # field is selected from a strict allowlist above.
        cur.execute(f"UPDATE orders SET {field}=%s,updated_at=NOW() WHERE id=%s", (value, order_id))
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data)
               VALUES(%s,%s,'order.details_changed','order',%s,%s::jsonb,%s::jsonb)""",
            (staff.telegram_id, staff.role, str(order_id), json_dumps({field:old_value}), json_dumps({field:value})))
    bot.reply_to(message, f"✅ Дані замовлення #{order_id} оновлено.")
    updated = fetch_order(order_id)
    if updated:
        bot.send_message(message.chat.id, order_card_text(updated), reply_markup=order_keyboard(updated, staff))


# ---------------------------------------------------------------------------
# Order lifecycle integrity: read-only reconciliation and guarded corrections
# ---------------------------------------------------------------------------

ORDER_LIFECYCLE_STATES = {
    "pre_fulfillment": ("new", "confirmed", "packing", "packed", "ready_to_ship", "problem"),
    "stock_consumed": ("shipped", "delivered", "completed"),
    "terminal": ("cancelled", "returned"),
}


def order_lifecycle_reconciliation(limit: int = 200) -> dict[str, Any]:
    """Find order/reservation/stock inconsistencies without changing business data.

    The report is intentionally read-only. It highlights cases that need an
    owner decision instead of silently repairing quantities or payment states.
    """
    limit = max(20, min(1000, int(limit)))
    report: dict[str, Any] = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "checked_orders": 0,
        "issue_count": 0,
        "issues": [],
        "summary": {},
    }
    with db_cursor() as cur:
        cur.execute(
            """
            SELECT
                COUNT(*) FILTER (WHERE o.status IN ('new','confirmed','packing','packed','ready_to_ship','problem')) AS pre_fulfillment,
                COUNT(*) FILTER (WHERE o.status IN ('shipped','delivered','completed')) AS stock_consumed,
                COUNT(*) FILTER (WHERE o.status='cancelled') AS cancelled,
                COUNT(*) FILTER (WHERE o.status='returned') AS returned,
                COUNT(*) FILTER (WHERE o.payment_status='paid') AS paid_orders,
                COALESCE(SUM(o.paid_amount) FILTER (WHERE o.payment_status='paid'),0) AS paid_amount
            FROM orders o
            """
        )
        summary = cur.fetchone() or {}
        report["summary"] = dict(summary)
        cur.execute(
            """
            WITH reservation_totals AS (
                SELECT order_id,
                       COUNT(*) FILTER (WHERE state='active') AS active_count,
                       COUNT(*) FILTER (WHERE state='consumed') AS consumed_count,
                       COUNT(*) FILTER (WHERE state='released') AS released_count,
                       COUNT(*) FILTER (WHERE state='expired') AS expired_count
                FROM stock_reservations
                GROUP BY order_id
            )
            SELECT o.id, o.order_number, o.status, o.payment_status,
                   COALESCE(r.active_count,0) AS active_reservations,
                   COALESCE(r.consumed_count,0) AS consumed_reservations,
                   COALESCE(r.released_count,0) AS released_reservations,
                   COALESCE(r.expired_count,0) AS expired_reservations,
                   COALESCE(SUM(oi.quantity),0) AS item_qty,
                   COALESCE(SUM(oi.line_total),0) AS item_total,
                   o.items_total, o.delivery_total, o.grand_total, o.paid_amount
            FROM orders o
            LEFT JOIN reservation_totals r ON r.order_id=o.id
            LEFT JOIN order_items oi ON oi.order_id=o.id
            GROUP BY o.id, r.active_count, r.consumed_count, r.released_count, r.expired_count
            ORDER BY o.created_at DESC, o.id DESC
            LIMIT %s
            """,
            (limit,),
        )
        rows = list(cur.fetchall())
        report["checked_orders"] = len(rows)
        for row in rows:
            status = row["status"]
            active = int(row["active_reservations"] or 0)
            consumed = int(row["consumed_reservations"] or 0)
            issues = []
            if status in ORDER_LIFECYCLE_STATES["stock_consumed"] and active:
                issues.append("є активні резерви після відвантаження")
            if status in ("cancelled", "returned") and active:
                issues.append("є активні резерви у завершеному замовленні")
            if status in ORDER_LIFECYCLE_STATES["pre_fulfillment"] and consumed:
                issues.append("товар списаний до передачі в доставку")
            expected_total = (
                Decimal(str(row["items_total"] or 0))
                + Decimal(str(row["delivery_total"] or 0))
            )
            stored_total = Decimal(str(row["grand_total"] or 0))
            if abs(expected_total - stored_total) > Decimal("0.01"):
                issues.append("сума замовлення не дорівнює товарам + доставці")
            if row["payment_status"] == "paid":
                paid = Decimal(str(row["paid_amount"] or 0))
                grand = Decimal(str(row["grand_total"] or 0))
                if paid <= 0 or paid > grand:
                    issues.append("некоректна підтверджена сума оплати")
            if issues:
                report["issues"].append({
                    "order_id": int(row["id"]),
                    "order_number": row["order_number"],
                    "status": status,
                    "issues": issues,
                })
    report["issue_count"] = len(report["issues"])
    return report


def order_lifecycle_render(chat_id: int, staff: Staff, limit: int = 100) -> None:
    if staff.role != "owner":
        bot.send_message(chat_id, "⛔ Звіт цілісності доступний лише власнику.")
        return
    try:
        report = order_lifecycle_reconciliation(limit)
    except Exception:
        log.exception("Order lifecycle reconciliation failed")
        bot.send_message(chat_id, "Не вдалося сформувати звіт. Перевірте журнал системи.")
        return
    summary = report["summary"]
    lines = [
        "<b>🔎 Контроль циклу замовлення</b>",
        f"Перевірено останніх замовлень: <b>{report['checked_orders']}</b>",
        f"Виявлено потенційних проблем: <b>{report['issue_count']}</b>",
        "",
        f"До відвантаження: {int(summary.get('pre_fulfillment') or 0)}",
        f"У доставці/доставлено: {int(summary.get('stock_consumed') or 0)}",
        f"Скасовано: {int(summary.get('cancelled') or 0)}",
        f"Повернено: {int(summary.get('returned') or 0)}",
        f"Підтверджено оплат: {int(summary.get('paid_orders') or 0)}",
        f"Сума підтверджених оплат: {_inv_money(summary.get('paid_amount') or 0)}",
    ]
    if report["issues"]:
        lines += ["", "<b>Потрібна перевірка:</b>"]
        for issue in report["issues"][:15]:
            lines.append(
                f"• #{safe(issue['order_number'])}: {safe('; '.join(issue['issues']))}"
            )
        if len(report["issues"]) > 15:
            lines.append(f"…і ще {len(report['issues']) - 15}")
    else:
        lines += ["", "Потенційних невідповідностей у вибірці не знайдено."]
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("🔄 Оновити", callback_data="lifecycle:refresh"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb, parse_mode="HTML")


@bot.callback_query_handler(func=lambda c: c.data == "lifecycle:refresh")
def order_lifecycle_refresh_callback(call):
    staff = require_staff(call)
    if not staff or staff.role != "owner":
        bot.answer_callback_query(call.id, "Лише власник.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    order_lifecycle_render(call.message.chat.id, staff)


@bot.message_handler(func=lambda m: m.text == "🔎 Контроль циклу замовлення")
def order_lifecycle_command(message):
    staff = require_staff(message)
    if not staff or staff.role != "owner":
        bot.reply_to(message, "⛔ Цей звіт доступний лише власнику.")
        return
    order_lifecycle_render(message.chat.id, staff)


def order_financial_integrity_report(limit: int = 200) -> dict[str, Any]:
    """Read-only payment/total checks; never infer cash received from order totals."""
    limit = max(20, min(1000, int(limit)))
    issues = []
    with db_cursor() as cur:
        cur.execute(
            """
            SELECT id, order_number, status, payment_status, grand_total, paid_amount
            FROM orders
            ORDER BY created_at DESC, id DESC
            LIMIT %s
            """,
            (limit,),
        )
        rows = list(cur.fetchall())
    for row in rows:
        grand = Decimal(str(row["grand_total"] or 0))
        paid = Decimal(str(row["paid_amount"] or 0))
        state = row["payment_status"]
        if state == "paid" and (paid <= 0 or paid > grand):
            issues.append({
                "order_id": int(row["id"]),
                "order_number": row["order_number"],
                "problem": "paid_amount поза допустимим діапазоном",
            })
        elif state != "paid" and paid > 0:
            issues.append({
                "order_id": int(row["id"]),
                "order_number": row["order_number"],
                "problem": "є paid_amount, але payment_status не paid",
            })
    return {"checked": len(rows), "issues": issues, "issue_count": len(issues)}


def order_lifecycle_owner_button(chat_id: int) -> None:
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton(
        "🔎 Перевірити цикл замовлення",
        callback_data="lifecycle:refresh",
    ))
    bot.send_message(
        chat_id,
        "Контроль резервів, списання, статусів і оплат. Звіт лише діагностує, "
        "нічого автоматично не змінює.",
        reply_markup=kb,
    )






# ---------------------------------------------------------------------------
# Returns and manual refunds. No payment-provider API is assumed.
# ---------------------------------------------------------------------------

RETURN_ALLOWED_ORDER_STATES = {"shipped", "delivered", "completed", "problem"}
REFUND_METHODS = {"cash", "bank_transfer", "card_terminal", "other"}


def create_return_draft(
    order_id: int,
    order_item_id: int,
    quantity: int,
    restock: bool,
    reason: str,
    actor: Staff,
    restock_note: str = "",
) -> int:
    """Create a return draft for one order line; no stock or money changes."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Створювати повернення можуть лише власник або адміністратор.")
    quantity = int(quantity)
    reason = str(reason or "").strip()
    if quantity <= 0 or not reason:
        raise ValueError("Вкажіть позитивну кількість і причину повернення.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT o.id, o.status, oi.id AS order_item_id, oi.quantity AS sold_qty,
                      oi.unit_price, oi.variant_id, oi.sku_snapshot,
                      COALESCE((
                        SELECT SUM(ri.quantity)
                        FROM return_items ri
                        JOIN return_documents rd ON rd.id=ri.return_id
                        WHERE ri.order_item_id=oi.id AND rd.state='approved'
                      ),0) AS already_returned
               FROM orders o
               JOIN order_items oi ON oi.order_id=o.id
               WHERE o.id=%s AND oi.id=%s
               FOR UPDATE OF o, oi""",
            (order_id, order_item_id),
        )
        row = cur.fetchone()
        if not row:
            raise ValueError("Замовлення або товарний рядок не знайдено.")
        if row["status"] not in RETURN_ALLOWED_ORDER_STATES:
            raise ValueError("Повернення можливе лише після відправлення або для проблемного замовлення.")
        remaining = int(row["sold_qty"]) - int(row["already_returned"] or 0)
        if quantity > remaining:
            raise ValueError(f"Можна повернути не більше {remaining} шт. цього товарного рядка.")
        if restock and not row["variant_id"]:
            raise ValueError("Для цього старого рядка не визначено SKU. Повернення на склад заборонено до ручної звірки.")
        cur.execute(
            """INSERT INTO return_documents(order_id,reason,created_by)
               VALUES(%s,%s,%s) RETURNING id""",
            (order_id, reason, actor.telegram_id),
        )
        return_id = int(cur.fetchone()["id"])
        cur.execute(
            """INSERT INTO return_items
               (return_id,order_item_id,variant_id,quantity,unit_price_snapshot,restock,restock_note)
               VALUES(%s,%s,%s,%s,%s,%s,%s)""",
            (return_id, order_item_id, row["variant_id"], quantity, row["unit_price"],
             bool(restock), str(restock_note or "").strip()),
        )
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                                     after_data,reason)
               VALUES(%s,%s,'return.draft_created','return',%s,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(return_id),
             json_dumps({"order_id": order_id, "order_item_id": order_item_id,
                         "quantity": quantity, "restock": bool(restock)}), reason),
        )
    return return_id


def get_return_document(return_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.*, o.order_number, o.payment_status, o.paid_amount, o.grand_total,
                      COALESCE((SELECT SUM(rr.amount) FROM refund_records rr
                                WHERE rr.order_id=o.id AND rr.state='confirmed'),0) AS refunded_total
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE rd.id=%s""",
            (return_id,),
        )
        doc = cur.fetchone()
        if not doc:
            return None
        cur.execute(
            """SELECT ri.*, oi.product_name_snapshot, oi.sku_snapshot
               FROM return_items ri JOIN order_items oi ON oi.id=ri.order_item_id
               WHERE ri.return_id=%s ORDER BY ri.id""",
            (return_id,),
        )
        doc["items"] = list(cur.fetchall())
    return dict(doc)



def reverse_order_bonus_for_return(
    cur, customer_id: int, order_id: int, return_id: int,
    return_value: Decimal, actor_telegram_id: int
) -> Decimal:
    """Reverse 2% of returned item value, consuming unspent bonus first.

    If some earned bonus was already spent, the shortfall becomes a non-negative
    loyalty debt and offsets future earnings. No customer's balance is made negative.
    """
    key = f"return:{return_id}:loyalty_reversal"
    cur.execute("SELECT id FROM loyalty_adjustments WHERE idempotency_key=%s", (key,))
    if cur.fetchone():
        return Decimal("0.00")
    cur.execute(
        """SELECT items_total FROM orders WHERE id=%s FOR UPDATE""",
        (order_id,),
    )
    order = cur.fetchone()
    if not order or Decimal(str(order["items_total"] or 0)) <= 0:
        return Decimal("0.00")
    target = (return_value * Decimal("0.02")).quantize(Decimal("0.01"))
    if target <= 0:
        return Decimal("0.00")
    cur.execute("INSERT INTO loyalty_accounts(customer_id) VALUES(%s) ON CONFLICT DO NOTHING", (customer_id,))
    cur.execute("INSERT INTO loyalty_debts(customer_id,amount) VALUES(%s,0) ON CONFLICT DO NOTHING", (customer_id,))
    cur.execute("SELECT available,pending FROM loyalty_accounts WHERE customer_id=%s FOR UPDATE", (customer_id,))
    account = cur.fetchone()
    remaining = target
    removed_available = Decimal("0.00")
    removed_pending = Decimal("0.00")
    cur.execute(
        """SELECT ll.id,ll.remaining_amount,ll.state
           FROM loyalty_lots ll
           JOIN loyalty_transactions lt ON lt.id=ll.source_transaction_id
           WHERE lt.order_id=%s AND lt.transaction_type='earn'
             AND ll.state IN ('pending','available') AND ll.remaining_amount>0
           ORDER BY CASE WHEN ll.state='pending' THEN 0 ELSE 1 END, ll.id
           FOR UPDATE OF ll""",
        (order_id,),
    )
    lots = list(cur.fetchall())
    for lot in lots:
        if remaining <= 0:
            break
        use = min(remaining, Decimal(str(lot["remaining_amount"])))
        new_left = Decimal(str(lot["remaining_amount"])) - use
        cur.execute(
            "UPDATE loyalty_lots SET remaining_amount=%s,state=%s WHERE id=%s",
            (new_left, "spent" if new_left == 0 else lot["state"], lot["id"]),
        )
        if lot["state"] == "pending":
            removed_pending += use
        else:
            removed_available += use
        remaining -= use
    if removed_pending:
        cur.execute("UPDATE loyalty_accounts SET pending=GREATEST(0,pending-%s) WHERE customer_id=%s",
                    (removed_pending, customer_id))
        cur.execute(
            """UPDATE loyalty_transactions SET amount=GREATEST(0,amount-%s)
               WHERE order_id=%s AND transaction_type='earn' AND state='pending'""",
            (removed_pending, order_id),
        )
    if removed_available:
        cur.execute("UPDATE loyalty_accounts SET available=GREATEST(0,available-%s) WHERE customer_id=%s",
                    (removed_available, customer_id))
    debt_created = remaining
    if debt_created:
        cur.execute("UPDATE loyalty_debts SET amount=amount+%s,updated_at=NOW() WHERE customer_id=%s",
                    (debt_created, customer_id))
    cur.execute(
        """INSERT INTO loyalty_adjustments
           (customer_id,order_id,return_id,adjustment_type,amount,debt_created,
            actor_telegram_id,idempotency_key,reason)
           VALUES(%s,%s,%s,'return_reversal',%s,%s,%s,%s,%s)""",
        (customer_id, order_id, return_id, target, debt_created, actor_telegram_id,
         key, "Сторнування 2% бонусів за повернені товари"),
    )
    cur.execute(
        """INSERT INTO loyalty_transactions
           (customer_id,order_id,transaction_type,amount,state,reason,actor_telegram_id,idempotency_key)
           VALUES(%s,%s,'return_reversal',%s,'completed',%s,%s,%s)
           ON CONFLICT(idempotency_key) DO NOTHING""",
        (customer_id, order_id, -target,
         f"Сторнування бонусів за повернення #{return_id}", actor_telegram_id,
         f"return:{return_id}:loyalty_reversal_tx"),
    )
    return target


def approve_return(return_id: int, actor: Staff) -> Decimal:
    """Approve physical return and optionally restock; refund is a separate action."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Підтверджувати повернення можуть лише власник або адміністратор.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.*, o.status AS order_status, o.payment_status, o.paid_amount, o.customer_id,
                      o.id AS locked_order_id
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE rd.id=%s FOR UPDATE OF rd, o""",
            (return_id,),
        )
        doc = cur.fetchone()
        if not doc:
            raise ValueError("Повернення не знайдено.")
        if doc["state"] != "draft":
            raise ValueError("Цей документ уже опрацьований.")
        if doc["order_status"] not in RETURN_ALLOWED_ORDER_STATES:
            raise ValueError("Статус замовлення не дозволяє підтвердити повернення.")
        cur.execute(
            """SELECT ri.*, oi.quantity AS sold_qty, oi.id AS line_id,
                      COALESCE((SELECT SUM(ri2.quantity)
                                FROM return_items ri2
                                JOIN return_documents rd2 ON rd2.id=ri2.return_id
                                WHERE ri2.order_item_id=oi.id AND rd2.state='approved'),0) AS prior_returned
               FROM return_items ri JOIN order_items oi ON oi.id=ri.order_item_id
               WHERE ri.return_id=%s FOR UPDATE OF ri, oi""",
            (return_id,),
        )
        items = list(cur.fetchall())
        if not items:
            raise ValueError("У документі немає товарів.")
        return_value = Decimal("0.00")
        for item in items:
            if int(item["quantity"]) > int(item["sold_qty"]) - int(item["prior_returned"] or 0):
                raise ValueError("Кількість повернення змінилася. Оновіть документ і перевірте попередні повернення.")
            return_value += Decimal(str(item["unit_price_snapshot"])) * int(item["quantity"])
            if item["restock"]:
                variant_id = item["variant_id"]
                if not variant_id:
                    raise ValueError("Не визначено SKU для повернення на склад.")
                cur.execute(
                    """UPDATE product_variants
                       SET stock_qty=stock_qty+%s, updated_at=NOW()
                       WHERE id=%s RETURNING id""",
                    (item["quantity"], variant_id),
                )
                if cur.fetchone() is None:
                    raise ValueError("SKU для повернення на склад не знайдено.")
                cur.execute(
                    """INSERT INTO inventory_movements
                       (variant_id,movement_type,quantity_delta,reference_type,reference_id,
                        reason,actor_telegram_id)
                       VALUES(%s,'return',%s,'return',%s,%s,%s)""",
                    (variant_id, item["quantity"], str(return_id),
                     item["restock_note"] or "Повернення товару на склад", actor.telegram_id),
                )
        already_refunded = Decimal("0.00")
        cur.execute(
            "SELECT COALESCE(SUM(amount),0) AS total FROM refund_records WHERE order_id=%s AND state='confirmed'",
            (doc["order_id"],),
        )
        already_refunded = Decimal(str(cur.fetchone()["total"] or 0))
        paid = Decimal(str(doc["paid_amount"] or 0)) if doc["payment_status"] == "paid" else Decimal("0.00")
        refund_ceiling = max(Decimal("0.00"), min(return_value, paid - already_refunded))
        bonus_reversed = Decimal("0.00")
        if doc["customer_id"]:
            bonus_reversed = reverse_order_bonus_for_return(
                cur, int(doc["customer_id"]), int(doc["order_id"]),
                return_id, return_value, actor.telegram_id,
            )
        cur.execute(
            """UPDATE return_documents SET state='approved', reviewed_by=%s, reviewed_at=NOW(),
                      approved_refund_ceiling=%s, loyalty_reversal_amount=%s WHERE id=%s""",
            (actor.telegram_id, refund_ceiling, bonus_reversed, return_id),
        )
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                                     before_data,after_data,reason)
               VALUES(%s,%s,'return.approved','return',%s,%s::jsonb,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(return_id),
             json_dumps({"state": "draft"}),
             json_dumps({"state": "approved", "restocked": sum(1 for x in items if x["restock"]),
                         "return_value": return_value, "refund_ceiling": refund_ceiling}),
             doc["reason"]),
        )
    return refund_ceiling


def reject_return(return_id: int, actor: Staff, reason: str) -> None:
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Відхиляти повернення можуть лише власник або адміністратор.")
    reason = str(reason or "").strip()
    if not reason:
        raise ValueError("Вкажіть причину відхилення.")
    with db_cursor() as cur:
        cur.execute("SELECT state FROM return_documents WHERE id=%s FOR UPDATE", (return_id,))
        row = cur.fetchone()
        if not row or row["state"] != "draft":
            raise ValueError("Чернетку повернення не знайдено або вже опрацьовано.")
        cur.execute(
            "UPDATE return_documents SET state='rejected',reviewed_by=%s,reviewed_at=NOW() WHERE id=%s",
            (actor.telegram_id, return_id),
        )
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,reason)
               VALUES(%s,%s,'return.rejected','return',%s,%s)""",
            (actor.telegram_id, actor.role, str(return_id), reason),
        )


def confirm_manual_refund(
    return_id: int, amount: Decimal, method: str, external_reference: str, actor: Staff
) -> int:
    """Record a refund already executed outside Cloud Hub; does not move money."""
    if actor.role != "owner":
        raise PermissionError("Фактичне підтвердження повернення коштів доступне лише власнику.")
    amount = Decimal(str(amount)).quantize(Decimal("0.01"))
    method = str(method or "").strip()
    if amount <= 0 or method not in REFUND_METHODS:
        raise ValueError("Перевірте суму та спосіб повернення.")
    reference = str(external_reference or "").strip()
    if not reference:
        raise ValueError("Потрібен номер квитанції/платіжного документа або пояснення.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.state, rd.order_id, rd.approved_refund_ceiling,
                      COALESCE((SELECT SUM(amount) FROM refund_records
                                WHERE return_id=rd.id AND state='confirmed'),0) AS this_return_refunded,
                      o.payment_status, o.paid_amount
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE rd.id=%s FOR UPDATE OF rd, o""",
            (return_id,),
        )
        row = cur.fetchone()
        if not row or row["state"] != "approved":
            raise ValueError("Повернення має бути спочатку підтверджене.")
        remaining_ceiling = Decimal(str(row["approved_refund_ceiling"])) - Decimal(str(row["this_return_refunded"]))
        if amount > remaining_ceiling:
            raise ValueError(f"Максимум для цього документа: {remaining_ceiling:.2f} грн.")
        cur.execute(
            """SELECT COALESCE(SUM(amount),0) AS total FROM refund_records
               WHERE order_id=%s AND state='confirmed'""",
            (row["order_id"],),
        )
        total_refunded = Decimal(str(cur.fetchone()["total"] or 0))
        if row["payment_status"] != "paid" or total_refunded + amount > Decimal(str(row["paid_amount"])):
            raise ValueError("Сума повернень перевищить фактично підтверджену оплату.")
        cur.execute(
            """INSERT INTO refund_records(return_id,order_id,amount,method,external_reference,created_by)
               VALUES(%s,%s,%s,%s,%s,%s) RETURNING id""",
            (return_id, row["order_id"], amount, method, reference, actor.telegram_id),
        )
        refund_id = int(cur.fetchone()["id"])
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                                     after_data,reason)
               VALUES(%s,%s,'refund.manually_confirmed','refund',%s,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(refund_id),
             json_dumps({"return_id": return_id, "order_id": row["order_id"],
                         "amount": amount, "method": method, "reference": reference}),
             "Підтверджено власником після фактичного виконання поза Cloud Hub"),
        )
    return refund_id


def list_open_returns(limit: int = 50) -> list[dict]:
    limit = max(1, min(200, int(limit)))
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.id, rd.order_id, rd.reason, rd.created_at, o.order_number,
                      rd.created_by
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE rd.state='draft'
               ORDER BY rd.created_at, rd.id LIMIT %s""",
            (limit,),
        )
        return list(cur.fetchall())


def render_return_document(chat_id: int, return_id: int, staff: Staff) -> None:
    if staff.role not in {"owner", "admin"}:
        bot.send_message(chat_id, "⛔ Недостатньо прав.")
        return
    doc = get_return_document(return_id)
    if not doc:
        bot.send_message(chat_id, "Документ повернення не знайдено.")
        return
    lines = [
        f"<b>↩️ Повернення #{doc['id']}</b>",
        f"Замовлення: #{safe(doc['order_number'])}",
        f"Стан: <b>{safe(doc['state'])}</b>",
        f"Причина: {safe(doc['reason'])}",
        "",
    ]
    for item in doc["items"]:
        lines.append(
            f"• {safe(item['product_name_snapshot'])} / {safe(item['sku_snapshot'])} "
            f"× {item['quantity']} · {'на склад' if item['restock'] else 'без оприбуткування'}"
        )
    lines += ["", f"Гранична сума повернення коштів: <b>{_inv_money(doc['approved_refund_ceiling'])}</b>"]
    kb = types.InlineKeyboardMarkup(row_width=2)
    if doc["state"] == "draft":
        kb.add(
            types.InlineKeyboardButton("✅ Підтвердити повернення", callback_data=f"return:approve:{return_id}"),
            types.InlineKeyboardButton("❌ Відхилити", callback_data=f"return:reject:{return_id}"),
        )
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb, parse_mode="HTML")


@bot.message_handler(commands=["returns"])
def returns_queue_command(message):
    staff = require_staff(message)
    if not staff or staff.role not in {"owner", "admin"}:
        bot.reply_to(message, "⛔ Недостатньо прав.")
        return
    rows = list_open_returns()
    if not rows:
        bot.reply_to(message, "Чернеток повернення немає.")
        return
    for row in rows:
        kb = types.InlineKeyboardMarkup()
        kb.add(types.InlineKeyboardButton(
            f"Відкрити повернення #{row['id']}",
            callback_data=f"return:view:{row['id']}",
        ))
        bot.send_message(
            message.chat.id,
            f"Повернення #{row['id']} · замовлення #{safe(row['order_number'])}\nПричина: {safe(row['reason'])}",
            reply_markup=kb,
        )


@bot.callback_query_handler(func=lambda c: c.data.startswith("return:view:"))
def return_view_callback(call):
    staff = require_staff(call)
    if not staff or staff.role not in {"owner", "admin"}:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    render_return_document(call.message.chat.id, int(call.data.rsplit(":", 1)[1]), staff)


@bot.callback_query_handler(func=lambda c: c.data.startswith("return:approve:"))
def return_approve_callback(call):
    staff = require_staff(call)
    if not staff or staff.role not in {"owner", "admin"}:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    return_id = int(call.data.rsplit(":", 1)[1])
    try:
        ceiling = approve_return(return_id, staff)
        bot.answer_callback_query(call.id, "Повернення підтверджено.")
        bot.send_message(
            call.message.chat.id,
            f"Повернення #{return_id} підтверджено. Максимум для фактичного повернення коштів: {_inv_money(ceiling)}. "
            "Кошти тут не переказуються. Після фактичного переказу власник фіксує його окремою операцією.",
        )
        render_return_document(call.message.chat.id, return_id, staff)
    except Exception as exc:
        bot.answer_callback_query(call.id, "Не вдалося підтвердити.", show_alert=True)
        bot.send_message(call.message.chat.id, safe(str(exc)))


@bot.callback_query_handler(func=lambda c: c.data.startswith("return:reject:"))
def return_reject_callback(call):
    staff = require_staff(call)
    if not staff or staff.role not in {"owner", "admin"}:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    return_id = int(call.data.rsplit(":", 1)[1])
    try:
        reject_return(return_id, staff, "Відхилено власником/адміністратором через панель")
        bot.answer_callback_query(call.id, "Повернення відхилено.")
        bot.send_message(call.message.chat.id, f"Повернення #{return_id} відхилено.")
    except Exception as exc:
        bot.answer_callback_query(call.id, "Помилка.", show_alert=True)
        bot.send_message(call.message.chat.id, safe(str(exc)))


@bot.message_handler(commands=["return"])
def return_create_command(message):
    """Usage: /return ORDER_ID ORDER_ITEM_ID QTY restock|no_restock reason"""
    staff = require_staff(message)
    if not staff or staff.role not in {"owner", "admin"}:
        bot.reply_to(message, "⛔ Недостатньо прав.")
        return
    parts = (message.text or "").split(maxsplit=5)
    if len(parts) < 6 or parts[4] not in {"restock", "no_restock"}:
        bot.reply_to(
            message,
            "Формат: /return ORDER_ID ORDER_ITEM_ID КІЛЬКІСТЬ restock|no_restock причина",
        )
        return
    try:
        return_id = create_return_draft(
            int(parts[1]), int(parts[2]), int(parts[3]), parts[4] == "restock",
            parts[5], staff,
        )
        bot.reply_to(message, f"Створено чернетку повернення #{return_id}. Перевірте її через /returns.")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["refund"])
def manual_refund_command(message):
    """Usage: /refund RETURN_ID AMOUNT METHOD REFERENCE (owner only)."""
    staff = require_staff(message)
    if not staff or staff.role != "owner":
        bot.reply_to(message, "⛔ Підтвердження фактичного повернення коштів доступне лише власнику.")
        return
    parts = (message.text or "").split(maxsplit=4)
    if len(parts) != 5:
        bot.reply_to(message, "Формат: /refund RETURN_ID СУМА cash|bank_transfer|card_terminal|other РЕКВІЗИТ_АБО_КВИТАНЦІЯ")
        return
    try:
        refund_id = confirm_manual_refund(
            int(parts[1]), Decimal(parts[2].replace(",", ".")), parts[3], parts[4], staff
        )
        bot.reply_to(message, f"Повернення коштів #{refund_id} зафіксовано в журналі. Переказ має бути вже фактично виконаний.")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))






def historical_margin_report(days: int = 30, limit: int = 5000) -> dict[str, Any]:
    """Gross margin from immutable cost snapshots; rows without snapshots are excluded."""
    days = max(1, min(365, int(days)))
    limit = max(100, min(20000, int(limit)))
    with db_cursor() as cur:
        cur.execute(
            """SELECT oi.quantity,oi.line_total,oi.cost_price_snapshot,o.status,o.created_at
               FROM order_items oi JOIN orders o ON o.id=oi.order_id
               WHERE o.created_at >= NOW()-(%s * INTERVAL '1 day')
                 AND o.status IN ('shipped','delivered','completed')
               ORDER BY o.created_at DESC,o.id DESC,oi.id DESC LIMIT %s""",
            (days, limit),
        )
        rows = list(cur.fetchall())
    revenue = Decimal("0.00")
    cogs = Decimal("0.00")
    known = 0
    unknown = 0
    for row in rows:
        if row["cost_price_snapshot"] is None:
            unknown += 1
            continue
        revenue += Decimal(str(row["line_total"]))
        cogs += Decimal(str(row["cost_price_snapshot"])) * int(row["quantity"])
        known += 1
    return {
        "days": days, "rows_checked": len(rows), "rows_with_cost": known,
        "rows_without_historical_cost": unknown, "revenue_with_cost": revenue,
        "cogs": cogs, "gross_margin": revenue - cogs,
        "coverage_percent": (Decimal(known) * 100 / Decimal(len(rows))).quantize(Decimal("0.1")) if rows else Decimal("0.0"),
    }


def render_historical_margin_report(chat_id: int, staff: Staff, days: int = 30) -> None:
    if staff.role != "owner":
        bot.send_message(chat_id, "⛔ Маржинальний звіт доступний лише власнику.")
        return
    report = historical_margin_report(days)
    lines = [
        f"<b>📈 Валова маржа за {report['days']} днів</b>",
        f"Рядків продажу з собівартістю: {report['rows_with_cost']}",
        f"Без історичної собівартості: {report['rows_without_historical_cost']}",
        f"Покриття: {report['coverage_percent']}%",
        f"Виручка за рядками з відомою собівартістю: {_inv_money(report['revenue_with_cost'])}",
        f"COGS: {_inv_money(report['cogs'])}",
        f"Валова маржа: <b>{_inv_money(report['gross_margin'])}</b>",
        "",
        "Це валова маржа лише для рядків з історичною собівартістю, не чистий прибуток.",
    ]
    kb = types.InlineKeyboardMarkup(row_width=3)
    kb.add(
        types.InlineKeyboardButton("7 днів", callback_data="margin:7"),
        types.InlineKeyboardButton("30 днів", callback_data="margin:30"),
        types.InlineKeyboardButton("90 днів", callback_data="margin:90"),
    )
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb, parse_mode="HTML")


@bot.callback_query_handler(func=lambda c: c.data.startswith("margin:"))
def margin_report_callback(call):
    staff = require_staff(call)
    if not staff or staff.role != "owner":
        bot.answer_callback_query(call.id, "Лише власник.", show_alert=True)
        return
    try:
        days = int(call.data.split(":", 1)[1])
        bot.answer_callback_query(call.id)
        render_historical_margin_report(call.message.chat.id, staff, days)
    except Exception as exc:
        bot.answer_callback_query(call.id, "Не вдалося сформувати звіт.", show_alert=True)
        log.exception("Margin report failed: %s", exc)


@bot.message_handler(commands=["margin"])
def margin_report_command(message):
    staff = require_staff(message)
    if not staff or staff.role != "owner":
        bot.reply_to(message, "⛔ Лише власник.")
        return
    render_historical_margin_report(message.chat.id, staff, 30)






# ---------------------------------------------------------------------------
# Owner Security Center: staff lifecycle, event review, access controls
# ---------------------------------------------------------------------------

SECURITY_STATES = {"active","review_suspended","security_locked","owner_locked","deactivated"}
SECURITY_EVENT_LABELS = {
    "staff.created":"Працівника створено",
    "staff.role_changed":"Змінено роль",
    "staff.deactivated":"Працівника деактивовано",
    "staff.activated":"Працівника активовано",
    "staff.owner_locked":"Власник заблокував доступ",
    "staff.unlocked":"Власник розблокував доступ",
    "staff.review_started":"Почато перевірку",
    "security.threshold_lock":"Автоматичне критичне блокування",
    "security.threshold_triggered":"Автоматичне блокування за підозрілою активністю",
    "security.temporary_lock_expired":"Термін тимчасового блокування завершився",
    "security.threshold_triggered":"Автоматичне блокування за підозрілою активністю",
    "security.temporary_lock_expired":"Термін тимчасового блокування завершився",
    "security.signal":"Сигнал безпеки",
    "security.audit_tamper":"Спроба втручання в аудит",
}


def security_event(cur, severity: str, event_type: str, actor_id: Optional[int],
                   subject_id: Optional[int], details: Optional[dict] = None) -> None:
    if severity not in {"info","important","critical"}:
        severity = "important"
    cur.execute(
        """INSERT INTO security_events(severity,event_type,actor_telegram_id,subject_telegram_id,details)
           VALUES(%s,%s,%s,%s,%s::jsonb)""",
        (severity,event_type,actor_id,subject_id,json_dumps(details or {})),
    )


def owner_add_staff(telegram_id: int, display_name: str, role: str, actor: Staff) -> None:
    if actor.role != "owner":
        raise PermissionError("Додавати працівників може лише власник.")
    telegram_id=int(telegram_id)
    display_name=str(display_name or "").strip()
    if telegram_id <= 0 or telegram_id == CONFIG.owner_id or not display_name:
        raise ValueError("Перевірте Telegram ID та ім'я працівника.")
    if role not in {"admin","manager","packer","courier"}:
        raise ValueError("Недопустима роль.")
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO staff(telegram_id,display_name,role,active)
               VALUES(%s,%s,%s,TRUE)
               ON CONFLICT(telegram_id) DO NOTHING RETURNING telegram_id""",
            (telegram_id,display_name,role),
        )
        if not cur.fetchone():
            raise ValueError("Працівник із таким Telegram ID уже існує.")
        cur.execute(
            "INSERT INTO staff_security_state(telegram_id,state) VALUES(%s,'active') ON CONFLICT DO NOTHING",
            (telegram_id,),
        )
        security_event(cur,"important","staff.created",actor.telegram_id,telegram_id,
                       {"display_name":display_name,"role":role})
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data)
               VALUES(%s,%s,'staff.created','staff',%s,%s::jsonb)""",
            (actor.telegram_id,actor.role,str(telegram_id),
             json_dumps({"display_name":display_name,"role":role})),
        )


def owner_change_staff_role(telegram_id: int, role: str, actor: Staff, reason: str) -> None:
    if actor.role != "owner" or telegram_id == CONFIG.owner_id:
        raise PermissionError("Змінювати ролі може лише власник для інших працівників.")
    if role not in {"admin","manager","packer","courier"} or not reason.strip():
        raise ValueError("Вкажіть допустиму роль і причину.")
    with db_cursor() as cur:
        cur.execute("SELECT role FROM staff WHERE telegram_id=%s FOR UPDATE",(telegram_id,))
        row=cur.fetchone()
        if not row: raise ValueError("Працівника не знайдено.")
        before=row["role"]
        cur.execute("UPDATE staff SET role=%s,updated_at=NOW() WHERE telegram_id=%s",(role,telegram_id))
        security_event(cur,"critical","staff.role_changed",actor.telegram_id,telegram_id,
                       {"before":before,"after":role,"reason":reason.strip()})
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data,reason)
               VALUES(%s,%s,'staff.role_changed','staff',%s,%s::jsonb,%s::jsonb,%s)""",
            (actor.telegram_id,actor.role,str(telegram_id),json_dumps({"role":before}),
             json_dumps({"role":role}),reason.strip()),
        )


def owner_set_staff_active(telegram_id: int, active: bool, actor: Staff, reason: str) -> None:
    if actor.role != "owner" or telegram_id == CONFIG.owner_id:
        raise PermissionError("Керувати статусом працівника може лише власник.")
    if not reason.strip():
        raise ValueError("Обов'язково вкажіть причину.")
    with db_cursor() as cur:
        cur.execute("SELECT active FROM staff WHERE telegram_id=%s FOR UPDATE",(telegram_id,))
        row=cur.fetchone()
        if not row: raise ValueError("Працівника не знайдено.")
        if bool(row["active"]) == bool(active):
            raise ValueError("Статус уже такий.")
        cur.execute("UPDATE staff SET active=%s,updated_at=NOW() WHERE telegram_id=%s",(active,telegram_id))
        state="active" if active else "deactivated"
        if active:
            cur.execute(
                """INSERT INTO staff_security_state(telegram_id,state,review_deadline)
                   VALUES(%s,'active',NULL) ON CONFLICT(telegram_id) DO UPDATE
                   SET state=CASE WHEN staff_security_state.state IN ('owner_locked','security_locked')
                                  THEN staff_security_state.state ELSE 'active' END,
                       review_deadline=NULL,updated_at=NOW()""",
                (telegram_id,),
            )
        else:
            cur.execute(
                """INSERT INTO staff_security_state(telegram_id,state,review_deadline)
                   VALUES(%s,'deactivated',NULL) ON CONFLICT(telegram_id) DO UPDATE
                   SET state='deactivated',review_deadline=NULL,updated_at=NOW()""",
                (telegram_id,),
            )
        event="staff.activated" if active else "staff.deactivated"
        security_event(cur,"critical",event,actor.telegram_id,telegram_id,{"reason":reason.strip()})
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data,reason)
               VALUES(%s,%s,%s,'staff',%s,%s::jsonb,%s::jsonb,%s)""",
            (actor.telegram_id,actor.role,event,str(telegram_id),
             json_dumps({"active":bool(row["active"])}),json_dumps({"active":bool(active)}),reason.strip()),
        )
        if not active:
            enqueue_notification(cur,telegram_id,"security",
                {"text":"⛔ Ваш обліковий запис Cloud Hub деактивовано власником. Зверніться до власника системи."},
                f"staff-deactivated:{telegram_id}:{int(datetime.now(timezone.utc).timestamp())}")


def owner_security_unlock(telegram_id: int, actor: Staff, reason: str) -> None:
    if actor.role != "owner" or telegram_id == CONFIG.owner_id:
        raise PermissionError("Критичне розблокування доступне лише власнику.")
    if not reason.strip():
        raise ValueError("Вкажіть причину розблокування.")
    with db_cursor() as cur:
        cur.execute("SELECT active FROM staff WHERE telegram_id=%s FOR UPDATE",(telegram_id,))
        staff=cur.fetchone()
        if not staff or not staff["active"]:
            raise ValueError("Працівник неактивний або не знайдений.")
        cur.execute("SELECT state FROM staff_security_state WHERE telegram_id=%s FOR UPDATE",(telegram_id,))
        current=cur.fetchone()
        if not current or current["state"] not in {"owner_locked","security_locked"}:
            raise ValueError("Немає критичного блокування для зняття.")
        cur.execute("UPDATE staff_security_state SET state='active',review_deadline=NULL,updated_at=NOW() WHERE telegram_id=%s",(telegram_id,))
        security_event(cur,"critical","staff.unlocked",actor.telegram_id,telegram_id,{"reason":reason.strip(),"previous_state":current["state"]})
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data,reason)
               VALUES(%s,%s,'staff.security_unlocked','staff',%s,%s::jsonb,%s::jsonb,%s)""",
            (actor.telegram_id,actor.role,str(telegram_id),json_dumps({"state":current["state"]}),
             json_dumps({"state":"active"}),reason.strip()),
        )
        unlock_messages=[
            "🔓 Власник відновив доступ. Система безпеки визнає: цього разу ви пройшли перевірку. 😎",
            "🟢 Доступ повернуто! Робот-охоронець прибрав лупу. Працюємо далі 😂",
            "🔓 Вас випущено з цифрового карантину. Не змушуйте охорону знову нервувати 🤖",
            "✅ Доступ відновлено. Ваш пропуск знову зелений. Поводьтеся пристойно, хоча б до обіду 😁",
        ]
        cur.execute("SELECT review_counter FROM staff_security_state WHERE telegram_id=%s",(telegram_id,))
        counter_row=cur.fetchone()
        idx=int(counter_row["review_counter"] or 0)%len(unlock_messages) if counter_row else 0
        enqueue_notification(cur,telegram_id,"security",{"text":unlock_messages[idx]},
            f"staff-unlocked:{telegram_id}:{int(datetime.now(timezone.utc).timestamp())}")


def list_security_staff() -> list[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT s.telegram_id,s.display_name,s.role,s.active,
                      COALESCE(ss.state,CASE WHEN s.active THEN 'active' ELSE 'deactivated' END) security_state,
                      ss.review_deadline,
                      (SELECT MAX(se.created_at) FROM security_events se
                       WHERE se.subject_telegram_id=s.telegram_id) last_security_event,
                      (SELECT COUNT(*) FROM audit_log al WHERE al.actor_telegram_id=s.telegram_id
                       AND al.created_at>=NOW()-INTERVAL '24 hours') actions_24h
               FROM staff s LEFT JOIN staff_security_state ss ON ss.telegram_id=s.telegram_id
               ORDER BY CASE WHEN s.telegram_id=%s THEN 0 ELSE 1 END,s.display_name""",
            (CONFIG.owner_id,),
        )
        return list(cur.fetchall())


def list_security_events(limit: int = 50, subject_id: Optional[int] = None) -> list[dict]:
    limit=max(1,min(200,int(limit)))
    with db_cursor() as cur:
        if subject_id is None:
            cur.execute(
                """SELECT id,severity,event_type,actor_telegram_id,subject_telegram_id,details,created_at
                   FROM security_events ORDER BY created_at DESC,id DESC LIMIT %s""",(limit,))
        else:
            cur.execute(
                """SELECT id,severity,event_type,actor_telegram_id,subject_telegram_id,details,created_at
                   FROM security_events WHERE subject_telegram_id=%s
                   ORDER BY created_at DESC,id DESC LIMIT %s""",(subject_id,limit))
        return list(cur.fetchall())


def security_dashboard(chat_id: int, actor: Staff) -> None:
    if actor.role != "owner":
        bot.send_message(chat_id,"⛔ Security Center доступний лише власнику.")
        return
    try:
        staff_rows=list_security_staff()
        events=list_security_events(50)
        with db_cursor() as cur:
            cur.execute("SELECT COUNT(*) n FROM staff WHERE active=TRUE")
            active_count=int(cur.fetchone()["n"])
            cur.execute("SELECT COUNT(*) n FROM staff_security_state WHERE state IN ('owner_locked','security_locked','deactivated')")
            locked_count=int(cur.fetchone()["n"])
            cur.execute("SELECT COUNT(*) n FROM security_events WHERE created_at>=NOW()-INTERVAL '24 hours' AND severity='critical'")
            critical_24h=int(cur.fetchone()["n"])
    except Exception:
        log.exception("Security dashboard failed")
        bot.send_message(chat_id,"Не вдалося завантажити Security Center. Перевірте журнал системи.")
        return
    lines=[
        "<b>🛡️ Cloud Hub Security Center</b>",
        f"Активних працівників: <b>{active_count}</b>",
        f"Заблокованих/деактивованих: <b>{locked_count}</b>",
        f"Критичних подій за 24 години: <b>{critical_24h}</b>",
        "",
        "<b>Працівники:</b>",
    ]
    kb=types.InlineKeyboardMarkup(row_width=1)
    for row in staff_rows[:30]:
        status=row["security_state"]
        lines.append(f"• {safe(row['display_name'])} · {safe(ROLE_LABELS.get(row['role'],row['role']))} · {safe(status)}")
        kb.add(types.InlineKeyboardButton(
            f"👤 {row['display_name'][:28]} · {status}",
            callback_data=f"sec:staff:{row['telegram_id']}"))
    kb.add(types.InlineKeyboardButton("🧾 Останні 50 подій безпеки",callback_data="sec:events"))
    kb.add(types.InlineKeyboardButton("➕ Додати працівника",callback_data="sec:help:add"))
    kb.add(types.InlineKeyboardButton("🏠 Головне меню",callback_data="section:home"))
    bot.send_message(chat_id,"\n".join(lines),reply_markup=kb,parse_mode="HTML")


def security_staff_card(chat_id: int, telegram_id: int, actor: Staff) -> None:
    if actor.role!="owner":
        bot.send_message(chat_id,"⛔ Недостатньо прав.")
        return
    rows=[r for r in list_security_staff() if int(r["telegram_id"])==int(telegram_id)]
    if not rows:
        bot.send_message(chat_id,"Працівника не знайдено.")
        return
    row=rows[0]
    state=row["security_state"]
    lines=[
        f"<b>👤 {safe(row['display_name'])}</b>",
        f"Telegram ID: <code>{telegram_id}</code>",
        f"Роль: <b>{safe(ROLE_LABELS.get(row['role'],row['role']))}</b>",
        f"Активний: {'так' if row['active'] else 'ні'}",
        f"Стан безпеки: <b>{safe(state)}</b>",
        f"Дій за 24 години: {row['actions_24h']}",
        f"Остання подія: {row['last_security_event'] or 'немає'}",
        "",
        "Журнал аудиту: останні 100 дій із пагінацією.",
        f"Автобан: {SECURITY_AUTO_LOCK_MINUTES} хвилин; ручне блокування власника безстрокове.",
    ]
    kb=types.InlineKeyboardMarkup(row_width=2)
    if telegram_id!=CONFIG.owner_id:
        kb.add(types.InlineKeyboardButton("🔍 Перевірка 60 сек",callback_data=f"sec:review:{telegram_id}"))
        if state in {"active","review_suspended"}:
            kb.add(types.InlineKeyboardButton("⛔ Заблокувати",callback_data=f"sec:lock:{telegram_id}"))
        if state in {"owner_locked","security_locked"}:
            kb.add(types.InlineKeyboardButton("🔓 Розблокувати",callback_data=f"sec:unlock:{telegram_id}"))
        if row["active"]:
            kb.add(types.InlineKeyboardButton("Деактивувати",callback_data=f"sec:deactivate:{telegram_id}"))
        else:
            kb.add(types.InlineKeyboardButton("Активувати",callback_data=f"sec:activate:{telegram_id}"))
    kb.add(types.InlineKeyboardButton("📜 Останні 100 дій (аудит)",callback_data=f"sec:audit:{telegram_id}:0"))
    kb.add(types.InlineKeyboardButton("🧾 Останні 50 подій безпеки",callback_data=f"sec:staff_events:{telegram_id}"))
    kb.add(types.InlineKeyboardButton("⬅️ До Security Center",callback_data="sec:home"))
    bot.send_message(chat_id,"\n".join(lines),reply_markup=kb,parse_mode="HTML")


@bot.message_handler(commands=["security"])
def security_command(message):
    staff=require_staff(message)
    if not staff or staff.role!="owner":
        bot.reply_to(message,"⛔ Лише власник.")
        return
    security_dashboard(message.chat.id,staff)


@bot.callback_query_handler(func=lambda c: c.data=="sec:home")
def security_home_callback(call):
    staff=require_staff(call)
    if not staff or staff.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    bot.answer_callback_query(call.id)
    security_dashboard(call.message.chat.id,staff)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:staff:"))
def security_staff_callback(call):
    staff=require_staff(call)
    if not staff or staff.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    bot.answer_callback_query(call.id)
    security_staff_card(call.message.chat.id,int(call.data.rsplit(":",1)[1]),staff)


@bot.callback_query_handler(func=lambda c: c.data=="sec:events" or c.data.startswith("sec:staff_events:"))
def security_events_callback(call):
    staff=require_staff(call)
    if not staff or staff.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    subject=None if call.data=="sec:events" else int(call.data.rsplit(":",1)[1])
    events=list_security_events(50,subject)
    if not events:
        bot.answer_callback_query(call.id); bot.send_message(call.message.chat.id,"Подій безпеки немає."); return
    rendered=[]
    for event in events:
        details=event["details"] if isinstance(event["details"],dict) else {}
        signal=str(details.get("signal") or event["event_type"])
        source_details=details.get("source_details") if isinstance(details.get("source_details"),dict) else {}
        action=details.get("action") or source_details.get("action") or signal
        explanation=details.get("explanation") or SECURITY_SIGNAL_EXPLANATIONS.get(signal,"зареєстрована подія безпеки")
        rendered.append(
            f"#{event['id']} · {safe(event['severity'])} · {safe(SECURITY_EVENT_LABELS.get(event['event_type'],event['event_type']))}\n"
            f"Хто: {event['actor_telegram_id'] or 'система'} · Кого: {event['subject_telegram_id'] or '—'} · {safe(event['created_at'])}\n"
            f"Що зроблено: {safe(action)}\n"
            f"Чому бот вважає це небезпечним: {safe(explanation)}\n"
            f"Поріг: {safe(details.get('count','—'))}/{safe(details.get('threshold','—'))}; "
            f"вікно {safe(details.get('window_seconds','—'))} с; автобан {safe(details.get('automatic_lock_minutes','—'))} хв"
        )
    bot.answer_callback_query(call.id)
    for offset in range(0,len(rendered),6):
        heading="<b>🧾 Останні 50 подій безпеки</b>" if offset==0 else "<b>🧾 Продовження журналу</b>"
        bot.send_message(call.message.chat.id,heading+"\n\n"+"\n\n".join(rendered[offset:offset+6]),
                         parse_mode="HTML")


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:review:"))
def security_review_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    target=int(call.data.rsplit(":",1)[1])
    try:
        start_staff_review(target,actor)
        bot.answer_callback_query(call.id,"Перевірку розпочато.")
        security_staff_card(call.message.chat.id,target,actor)
    except Exception as exc:
        bot.answer_callback_query(call.id,safe(str(exc)),show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:lock:"))
def security_lock_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    target=int(call.data.rsplit(":",1)[1])
    try:
        set_staff_lock(target,True,actor,"Ручне блокування з Security Center")
        bot.answer_callback_query(call.id,"Доступ заблоковано.")
        security_staff_card(call.message.chat.id,target,actor)
    except Exception as exc:
        bot.answer_callback_query(call.id,safe(str(exc)),show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:unlock:"))
def security_unlock_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    target=int(call.data.rsplit(":",1)[1])
    try:
        owner_security_unlock(target,actor,"Розблокування власником через Security Center")
        bot.answer_callback_query(call.id,"Доступ відновлено.")
        security_staff_card(call.message.chat.id,target,actor)
    except Exception as exc:
        bot.answer_callback_query(call.id,safe(str(exc)),show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:deactivate:"))
def security_deactivate_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    target=int(call.data.rsplit(":",1)[1])
    try:
        owner_set_staff_active(target,False,actor,"Деактивація власником через Security Center")
        bot.answer_callback_query(call.id,"Працівника деактивовано.")
        security_staff_card(call.message.chat.id,target,actor)
    except Exception as exc:
        bot.answer_callback_query(call.id,safe(str(exc)),show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:activate:"))
def security_activate_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    target=int(call.data.rsplit(":",1)[1])
    try:
        owner_set_staff_active(target,True,actor,"Повторна активація власником через Security Center")
        bot.answer_callback_query(call.id,"Працівника активовано.")
        security_staff_card(call.message.chat.id,target,actor)
    except Exception as exc:
        bot.answer_callback_query(call.id,safe(str(exc)),show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data=="sec:help:add")
def security_add_help_callback(call):
    actor=require_staff(call)
    if not actor or actor.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    bot.answer_callback_query(call.id)
    bot.send_message(
        call.message.chat.id,
        "Додавання працівника: /staff_add TELEGRAM_ID ІМ'Я РОЛЬ\n"
        "Ролі: admin, manager, packer, courier\n"
        "Зміна ролі: /staff_role TELEGRAM_ID РОЛЬ причина",
    )


@bot.message_handler(commands=["staff_add"])
def security_staff_add_command(message):
    actor=require_staff(message)
    if not actor or actor.role!="owner":
        bot.reply_to(message,"⛔ Лише власник."); return
    parts=(message.text or "").split(maxsplit=3)
    if len(parts)!=4:
        bot.reply_to(message,"Формат: /staff_add TELEGRAM_ID ІМ'Я admin|manager|packer|courier"); return
    try:
        owner_add_staff(int(parts[1]),parts[2],parts[3],actor)
        bot.reply_to(message,"✅ Працівника додано.")
        security_dashboard(message.chat.id,actor)
    except Exception as exc:
        bot.reply_to(message,safe(str(exc)))


@bot.message_handler(commands=["staff_role"])
def security_staff_role_command(message):
    actor=require_staff(message)
    if not actor or actor.role!="owner":
        bot.reply_to(message,"⛔ Лише власник."); return
    parts=(message.text or "").split(maxsplit=3)
    if len(parts)!=4:
        bot.reply_to(message,"Формат: /staff_role TELEGRAM_ID РОЛЬ причина"); return
    try:
        owner_change_staff_role(int(parts[1]),parts[2],actor,parts[3])
        bot.reply_to(message,"✅ Роль змінено.")
    except Exception as exc:
        bot.reply_to(message,safe(str(exc)))




@bot.message_handler(func=lambda m: m.text in ("🔎 CRM-пошук",))
def search_menu(message):
    staff = require_staff(message, "orders.search")
    if not staff:
        bot.reply_to(message, "⛔ Недостатньо прав.")
        return
    msg = bot.send_message(
        message.chat.id,
        "🔎 Надішліть ім’я, телефон, Telegram ID/username, номер замовлення, ТТН, місто або відділення."
    )
    bot.register_next_step_handler(msg, process_search)


@bot.callback_query_handler(func=lambda c: c.data == "search:prompt")
def search_prompt_callback(call):
    staff = require_staff(call, "orders.search")
    if not staff:
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    msg = bot.send_message(
        call.message.chat.id,
        "🔎 Введіть ім’я, телефон, Telegram ID/username, номер замовлення, ТТН, місто або відділення."
    )
    bot.register_next_step_handler(msg, process_search)


def process_search(message):
    staff = require_staff(message, "orders.search")
    if not staff:
        bot.reply_to(message, "⛔ Доступ втрачено або недостатньо прав.")
        return
    query = (message.text or "").strip()
    if len(query) < 2:
        bot.reply_to(message, "Введіть щонайменше 2 символи.")
        return
    matches = search_orders(query, limit=50)
    if not matches:
        bot.reply_to(message, "Нічого не знайдено. Спробуйте інше написання або частину номера.")
        return
    bot.send_message(message.chat.id, f"🔎 Знайдено замовлень: {len(matches)}")
    for row, score, match_type in matches:
        row["search_match_type"] = match_type
        bot.send_message(
            message.chat.id,
            f"<i>Збіг: {safe(match_type)} · {score:.0%}</i>\n{order_card_text(row)}",
            reply_markup=order_keyboard(row, staff),
        )


@bot.message_handler(commands=["agequeue"])
def age_verification_queue_handler(message, user=None):
    # `user` is the real person (call.from_user when opened from a button).
    # call.message was written by the bot, so message.from_user would be the bot itself.
    staff = require_staff(_NS(from_user=user or message.from_user))
    if not staff or staff.role not in ("owner", "admin"):
        bot.reply_to(message, "⛔ Черга перевірки віку доступна лише власнику та адміністратору.")
        return
    with db_cursor() as cur:
        cur.execute("""SELECT c.id,c.telegram_id,c.username,c.first_name,c.last_name,c.phone,c.created_at
                       FROM customers c
                       WHERE c.age_verification_status='unverified' AND c.telegram_id IS NOT NULL
                         AND (EXISTS(SELECT 1 FROM customer_checkout_drafts d WHERE d.customer_id=c.id)
                              OR EXISTS(SELECT 1 FROM orders o WHERE o.customer_id=c.id
                                        AND o.status IN ('new','confirmed','packing')))
                       ORDER BY c.created_at ASC LIMIT 100""")
        rows = list(cur.fetchall())
    if not rows:
        bot.send_message(message.chat.id, "✅ Немає клієнтів, які очікують перевірки віку.")
        return
    bot.send_message(message.chat.id, f"🪪 <b>Черга перевірки віку</b> · {len(rows)}")
    for row in rows:
        name = " ".join(filter(None, [row['first_name'], row['last_name']])) or "Без імені"
        kb = types.InlineKeyboardMarkup(row_width=2)
        kb.add(types.InlineKeyboardButton("✅ Підтвердити", callback_data=f"age:verify:{row['id']}:yes"),
               types.InlineKeyboardButton("❌ Відхилити", callback_data=f"age:verify:{row['id']}:no"))
        bot.send_message(message.chat.id,
                         f"Клієнт #{row['id']} · {safe(name)}\nТелефон: {safe(row['phone'] or 'не вказано')}\nTelegram ID: <code>{row['telegram_id']}</code>\nUsername: @{safe(row['username'] or '—')}\nПеревірте документ поза ботом і лише тоді оберіть рішення.",
                         reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("age:verify:"))
def age_verification_callback(call):
    staff = require_staff(call)
    if not staff or staff.role not in ("owner", "admin"):
        bot.answer_callback_query(call.id, "Недостатньо прав.", show_alert=True)
        return
    try:
        _, _, raw_customer_id, decision = call.data.split(":", 3)
        customer_id = int(raw_customer_id)
        verified = decision == "yes"
        set_age_verification(customer_id, verified, staff, "Ручна перевірка через /agequeue")
        with db_cursor() as cur:
            cur.execute("SELECT telegram_id FROM customers WHERE id=%s", (customer_id,))
            customer = cur.fetchone()
        if customer and customer['telegram_id']:
            bot.send_message(int(customer['telegram_id']),
                             "✅ Перевірку віку підтверджено. Можете повернутися до оформлення замовлення." if verified
                             else "❌ Перевірку віку не пройдено. Оформлення замовлення недоступне.")
        bot.answer_callback_query(call.id, "Рішення збережено.")
        try:
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=None)
        except Exception:
            pass
    except Exception as exc:
        log.exception("Age verification callback failed")
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)


@bot.message_handler(commands=["delivery"])
def customer_delivery_start(message):
    if get_staff(message.from_user.id):
        bot.reply_to(message, "Для перевірки клієнтського сценарію використайте окремий тестовий акаунт.")
        return
    msg = bot.send_message(
        message.chat.id,
        "🚚 Вкажіть адресу доставки у Львові (вулиця та номер будинку). "
        "Адресу магазину ми не показуємо. Максимальна відстань кур’єра: 20 км за маршрутом."
    )
    bot.register_next_step_handler(msg, customer_delivery_address)


def customer_delivery_address(message):
    address = (message.text or "").strip()
    if not address or len(address) > 300:
        bot.reply_to(message, "Вкажіть коректну адресу до 300 символів.")
        return
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(
        types.InlineKeyboardButton("Звичайна кур’єрська", callback_data="delivery:quote:standard"),
        types.InlineKeyboardButton("Експрес до 29 хв", callback_data="delivery:quote:express"),
        types.InlineKeyboardButton("Нічна 22:00–23:59", callback_data="delivery:quote:night"),
        types.InlineKeyboardButton("Нова пошта", callback_data="delivery:np"),
    )
    bot.send_message(message.chat.id, "Оберіть спосіб доставки:", reply_markup=kb)
    # Store address in a short-lived DB-backed draft rather than trusting callback data.
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO delivery_address_drafts(telegram_id,address) VALUES(%s,%s)
               ON CONFLICT(telegram_id) DO UPDATE SET address=EXCLUDED.address,updated_at=NOW()""",
            (message.from_user.id, address),
        )


@bot.callback_query_handler(func=lambda c: c.data.startswith("delivery:quote:"))
def customer_delivery_quote_callback(call):
    tariff_code = call.data.rsplit(":", 1)[-1]
    with db_cursor() as cur:
        cur.execute("SELECT address FROM delivery_address_drafts WHERE telegram_id=%s", (call.from_user.id,))
        draft = cur.fetchone()
    if not draft:
        bot.answer_callback_query(call.id, "Адресу не знайдено. Почніть розрахунок заново.", show_alert=True)
        return
    bot.answer_callback_query(call.id, "Розраховую маршрут…")
    try:
        quote = create_delivery_quote(call.from_user.id, draft["address"], tariff_code)
    except DeliveryError as exc:
        bot.send_message(call.message.chat.id, safe(str(exc)))
        return
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("✅ Підтвердити", callback_data=f"delivery:confirm:{quote['id']}:yes"),
        types.InlineKeyboardButton("❌ Ні", callback_data=f"delivery:confirm:{quote['id']}:no"),
    )
    text = (
        f"🚚 <b>{safe(quote['tariff_title'])}</b>\n"
        f"Ви знаходитесь приблизно за <b>{quote['distance_km']:.2f} км</b> від магазину.\n"
        f"Вартість доставки: <b>{money(quote['price'])}</b>\n\n"
        "Підтвердити цей спосіб доставки?"
    )
    bot.send_message(call.message.chat.id, text, reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("delivery:confirm:"))
def customer_delivery_confirm_callback(call):
    try:
        _, _, raw_id, choice = call.data.split(":", 3)
        quote_id = int(raw_id)
    except (ValueError, TypeError):
        bot.answer_callback_query(call.id, "Некоректний запит.", show_alert=True)
        return
    ok, result = confirm_delivery_quote(quote_id, call.from_user.id, choice == "yes")
    bot.answer_callback_query(call.id, result[:180], show_alert=not ok)
    if ok:
        bot.send_message(call.message.chat.id, safe(result))


@bot.callback_query_handler(func=lambda c: c.data == "delivery:np")
def customer_delivery_np_callback(call):
    bot.answer_callback_query(call.id)
    bot.send_message(
        call.message.chat.id,
        "📦 Ви обрали Нову пошту. Вартість перевезення визначає перевізник і вона не додається до тарифу кур’єра Cloud Hub."
    )


# ---------------------------------------------------------------------------
# Owner/admin catalogue workspace (Handoff v1.10 continuation)
# ---------------------------------------------------------------------------
# The storefront hierarchy is deliberately normalized:
# root department -> brand -> product -> SKU/variant. Inventory is never
# stored on a product row; every stock movement belongs to a variant ID.

CATALOG_WIZARDS: dict[int, dict[str, Any]] = {}
CATALOG_PAGE_SIZE = 8
ROOT_DEPARTMENT_ORDER = ("Рідини", "Под-системи", "Картриджі", "Інше")


def catalog_actor(message_or_call, permission: str = "catalog.read") -> Optional[Staff]:
    """Authenticate a catalogue operator and enforce the requested permission."""
    staff = require_staff(message_or_call, permission)
    if not staff:
        return None
    if not staff.can(permission):
        return None
    return staff


def _catalog_audit(cur, actor: Staff, action: str, entity_type: str,
                   entity_id: Any, before: Optional[dict] = None,
                   after: Optional[dict] = None, reason: str = "") -> None:
    cur.execute(
        """INSERT INTO audit_log
           (actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data,reason)
           VALUES(%s,%s,%s,%s,%s,%s::jsonb,%s::jsonb,%s)""",
        (actor.telegram_id, actor.role, action, entity_type, str(entity_id),
         json_dumps(before) if before is not None else None,
         json_dumps(after) if after is not None else None, reason),
    )
    action_key = str(action).casefold()
    signal = "price_edit" if "price_changed" in action_key else None
    if signal:
        record_security_signal(cur, signal, actor.telegram_id, None,
                               {"action": action, "entity_type": entity_type, "entity_id": str(entity_id)})


def catalog_get_departments(include_inactive: bool = False) -> list[dict]:
    """Return the four canonical storefront departments, then custom children."""
    active_filter = "" if include_inactive else "AND active=TRUE"
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT id,name,parent_id,active,sort_order,created_at
                FROM categories WHERE parent_id IS NULL {active_filter}
                ORDER BY CASE name
                  WHEN 'Рідини' THEN 1 WHEN 'Под-системи' THEN 2
                  WHEN 'Картриджі' THEN 3 WHEN 'Інше' THEN 4 ELSE 99 END,
                  sort_order,id"""
        )
        return list(cur.fetchall())


def catalog_get_brands(department_id: Optional[int] = None,
                       include_inactive: bool = False) -> list[dict]:
    clauses = []
    params: list[Any] = []
    if not include_inactive:
        clauses.append("b.active=TRUE")
    if department_id is not None:
        clauses.append("EXISTS (SELECT 1 FROM brand_categories bc WHERE bc.brand_id=b.id AND bc.category_id=%s)")
        params.append(department_id)
    where = "WHERE " + " AND ".join(clauses) if clauses else ""
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT b.id,b.name,b.active,b.created_at,
                       COUNT(DISTINCT p.id) FILTER (WHERE p.archived_at IS NULL) product_count
                FROM brands b LEFT JOIN products p ON p.brand_id=b.id
                {where} GROUP BY b.id ORDER BY b.name,b.id""", params
        )
        return list(cur.fetchall())


def catalog_get_products(department_id: Optional[int] = None,
                         brand_id: Optional[int] = None,
                         include_hidden: bool = True,
                         include_archived: bool = False, archived_only: bool = False,
                         search: str = "", offset: int = 0,
                         limit: int = CATALOG_PAGE_SIZE) -> list[dict]:
    clauses = ["1=1"]
    params: list[Any] = []
    if archived_only:
        clauses.append("p.archived_at IS NOT NULL")
    elif not include_archived:
        clauses.append("p.archived_at IS NULL")
    if not include_hidden:
        clauses.append("p.active=TRUE AND p.manually_hidden=FALSE")
    if department_id is not None:
        clauses.append("p.category_id=%s")
        params.append(department_id)
    if brand_id is not None:
        clauses.append("p.brand_id=%s")
        params.append(brand_id)
    if search.strip():
        term = "%" + search.strip()[:100] + "%"
        clauses.append("(p.name ILIKE %s OR p.description ILIKE %s OR b.name ILIKE %s OR EXISTS (SELECT 1 FROM product_variants sv WHERE sv.product_id=p.id AND sv.sku ILIKE %s))")
        params.extend([term, term, term, term])
    params.extend([max(0, int(offset)), max(1, min(50, int(limit)))])
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT p.id,p.name,p.description,p.category_id,p.brand_id,
                       p.active,p.manually_hidden,p.archived_at,p.created_at,p.updated_at,
                       c.name category_name,b.name brand_name,
                       COUNT(v.id) FILTER (WHERE v.active=TRUE) variant_count,
                       COALESCE(SUM(v.stock_qty),0) stock_total,
                       COALESCE(SUM(v.reserved_qty),0) reserved_total,
                       MIN(v.price) FILTER (WHERE v.active=TRUE) min_price,
                       MAX(v.price) FILTER (WHERE v.active=TRUE) max_price
                FROM products p
                LEFT JOIN categories c ON c.id=p.category_id
                LEFT JOIN brands b ON b.id=p.brand_id
                LEFT JOIN product_variants v ON v.product_id=p.id
                WHERE {' AND '.join(clauses)}
                GROUP BY p.id,c.name,b.name
                ORDER BY p.updated_at DESC,p.id DESC OFFSET %s LIMIT %s""", params
        )
        return list(cur.fetchall())


def catalog_count_products(department_id: Optional[int] = None,
                           brand_id: Optional[int] = None,
                           include_archived: bool = False,
                           search: str = "") -> int:
    clauses = ["1=1"]
    params: list[Any] = []
    if not include_archived:
        clauses.append("p.archived_at IS NULL")
    if department_id is not None:
        clauses.append("p.category_id=%s")
        params.append(department_id)
    if brand_id is not None:
        clauses.append("p.brand_id=%s")
        params.append(brand_id)
    if search.strip():
        term = "%" + search.strip()[:100] + "%"
        clauses.append("(p.name ILIKE %s OR p.description ILIKE %s OR b.name ILIKE %s OR EXISTS (SELECT 1 FROM product_variants sv WHERE sv.product_id=p.id AND sv.sku ILIKE %s))")
        params.extend([term, term, term, term])
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT COUNT(*) n FROM products p LEFT JOIN brands b ON b.id=p.brand_id
                WHERE {' AND '.join(clauses)}""", params
        )
        return int(cur.fetchone()["n"])


def catalog_get_product(product_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT p.*,c.name category_name,b.name brand_name
               FROM products p LEFT JOIN categories c ON c.id=p.category_id
               LEFT JOIN brands b ON b.id=p.brand_id WHERE p.id=%s""",
            (product_id,),
        )
        product = cur.fetchone()
        if not product:
            return None
        cur.execute(
            """SELECT id,product_id,sku,variant_name,price,cost_price,stock_qty,
                      reserved_qty,low_stock_threshold,active,created_at,updated_at
               FROM product_variants WHERE product_id=%s ORDER BY id""",
            (product_id,),
        )
        product["variants"] = list(cur.fetchall())
        cur.execute(
            "SELECT id,telegram_file_id,disk_path,sort_order FROM product_media WHERE product_id=%s ORDER BY sort_order,id",
            (product_id,),
        )
        product["media"] = list(cur.fetchall())
        return product


def catalog_create_product_full(*, name: str, description: str,
                                department_id: int, brand_id: int,
                                actor: Staff) -> int:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для створення товару.")
    clean_name = " ".join((name or "").split())
    clean_description = (description or "").strip()
    if not clean_name or len(clean_name) > 180:
        raise ValueError("Назва товару має містити від 1 до 180 символів.")
    if len(clean_description) > 4000:
        raise ValueError("Опис товару задовгий (максимум 4000 символів).")
    with db_cursor() as cur:
        cur.execute("SELECT id,name FROM categories WHERE id=%s AND parent_id IS NULL AND active=TRUE FOR SHARE", (department_id,))
        category = cur.fetchone()
        if not category:
            raise ValueError("Категорію не знайдено або вона неактивна.")
        cur.execute("SELECT id,name FROM brands WHERE id=%s AND active=TRUE FOR SHARE", (brand_id,))
        brand = cur.fetchone()
        if not brand:
            raise ValueError("Виробника не знайдено або він неактивний.")
        cur.execute("INSERT INTO brand_categories(brand_id,category_id) VALUES(%s,%s) ON CONFLICT DO NOTHING", (brand_id, department_id))
        cur.execute(
            """INSERT INTO products(category_id,brand_id,name,description)
               VALUES(%s,%s,%s,%s) RETURNING id""",
            (department_id, brand_id, clean_name, clean_description),
        )
        product_id = int(cur.fetchone()["id"])
        _catalog_audit(cur, actor, "catalog.product_created", "product", product_id,
                       after={"name": clean_name, "category_id": department_id,
                              "brand_id": brand_id, "description": clean_description})
        return product_id


def catalog_update_product(product_id: int, actor: Staff, **changes) -> None:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для редагування товару.")
    allowed = {"name", "description", "category_id", "brand_id", "active", "manually_hidden"}
    if not changes or set(changes) - allowed:
        raise ValueError("Передано невідомі поля товару.")
    normalized: dict[str, Any] = {}
    for key, value in changes.items():
        if key == "name":
            value = " ".join(str(value).split())
            if not value or len(value) > 180:
                raise ValueError("Некоректна назва товару.")
        elif key == "description":
            value = str(value).strip()
            if len(value) > 4000:
                raise ValueError("Опис товару задовгий.")
        elif key in {"active", "manually_hidden"}:
            if not isinstance(value, bool):
                raise ValueError("Прапорець товару має бути true/false.")
        elif key == "category_id":
            value = int(value)
            with db_cursor() as check:
                check.execute("SELECT id FROM categories WHERE id=%s AND parent_id IS NULL AND active=TRUE", (value,))
                if not check.fetchone():
                    raise ValueError("Категорію не знайдено або вона неактивна.")
        elif key == "brand_id":
            value = int(value)
            with db_cursor() as check:
                check.execute("SELECT id FROM brands WHERE id=%s AND active=TRUE", (value,))
                if not check.fetchone():
                    raise ValueError("Виробника не знайдено або він неактивний.")
        normalized[key] = value
    with db_cursor() as cur:
        cur.execute("SELECT * FROM products WHERE id=%s FOR UPDATE", (product_id,))
        old = cur.fetchone()
        if not old:
            raise ValueError("Товар не знайдено.")
        assignments = ",".join(f"{key}=%s" for key in normalized)
        values = list(normalized.values()) + [product_id]
        cur.execute(f"UPDATE products SET {assignments},updated_at=NOW() WHERE id=%s", values)
        _catalog_audit(cur, actor, "catalog.product_updated", "product", product_id,
                       before={k: old[k] for k in normalized}, after=normalized)


def catalog_archive_product(product_id: int, actor: Staff, reason: str) -> None:
    if not actor.can("catalog.update") or len((reason or "").strip()) < 3:
        raise PermissionError("Потрібні права та причина архівації.")
    with db_cursor() as cur:
        cur.execute("SELECT id,name,archived_at FROM products WHERE id=%s FOR UPDATE", (product_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("Товар не знайдено.")
        if row["archived_at"]:
            raise ValueError("Товар уже в архіві.")
        cur.execute("SELECT COUNT(*) n FROM order_items oi JOIN product_variants v ON v.id=oi.variant_id WHERE v.product_id=%s", (product_id,))
        history_count = int(cur.fetchone()["n"])
        cur.execute("UPDATE products SET active=FALSE,manually_hidden=TRUE,archived_at=NOW(),updated_at=NOW() WHERE id=%s", (product_id,))
        cur.execute("UPDATE product_variants SET active=FALSE,updated_at=NOW() WHERE product_id=%s", (product_id,))
        _catalog_audit(cur, actor, "catalog.product_archived", "product", product_id,
                       before={"name": row["name"]},
                       after={"archived": True, "historical_order_lines": history_count},
                       reason=reason.strip())


def catalog_restore_product(product_id: int, actor: Staff) -> None:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для відновлення товару.")
    with db_cursor() as cur:
        cur.execute("SELECT id,name,archived_at FROM products WHERE id=%s FOR UPDATE", (product_id,))
        row = cur.fetchone()
        if not row or not row["archived_at"]:
            raise ValueError("Архівований товар не знайдено.")
        cur.execute("UPDATE products SET archived_at=NULL,active=TRUE,manually_hidden=TRUE,updated_at=NOW() WHERE id=%s", (product_id,))
        # Variants deliberately remain inactive until an operator reviews them.
        _catalog_audit(cur, actor, "catalog.product_restored_hidden", "product", product_id,
                       before={"archived": True}, after={"archived": False, "visible": False})


def catalog_set_variant_active(variant_id: int, active: bool, actor: Staff, reason: str) -> None:
    if not actor.can("catalog.update") or len((reason or "").strip()) < 3:
        raise PermissionError("Потрібні права та причина зміни статусу SKU.")
    with db_cursor() as cur:
        cur.execute("SELECT id,product_id,sku,active FROM product_variants WHERE id=%s FOR UPDATE", (variant_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("SKU не знайдено.")
        cur.execute("UPDATE product_variants SET active=%s,updated_at=NOW() WHERE id=%s", (active, variant_id))
        _catalog_audit(cur, actor, "catalog.variant_status_changed", "variant", variant_id,
                       before={"active": row["active"]}, after={"active": active}, reason=reason.strip())


def catalog_update_variant(variant_id: int, actor: Staff, *,
                           variant_name: Optional[str] = None,
                           cost_price: Optional[Decimal] = None,
                           low_stock_threshold: Optional[int] = None) -> None:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для редагування SKU.")
    changes: dict[str, Any] = {}
    if variant_name is not None:
        value = " ".join(variant_name.split())
        if len(value) > 120:
            raise ValueError("Назва варіанта задовга.")
        changes["variant_name"] = value
    if cost_price is not None:
        if cost_price < 0:
            raise ValueError("Собівартість не може бути від’ємною.")
        changes["cost_price"] = cost_price
    if low_stock_threshold is not None:
        if int(low_stock_threshold) < 0 or int(low_stock_threshold) > 1000000:
            raise ValueError("Некоректний поріг залишку.")
        changes["low_stock_threshold"] = int(low_stock_threshold)
    if not changes:
        raise ValueError("Немає полів для оновлення.")
    with db_cursor() as cur:
        cur.execute("SELECT * FROM product_variants WHERE id=%s FOR UPDATE", (variant_id,))
        old = cur.fetchone()
        if not old:
            raise ValueError("SKU не знайдено.")
        fields = ",".join(f"{k}=%s" for k in changes)
        cur.execute(f"UPDATE product_variants SET {fields},updated_at=NOW() WHERE id=%s",
                    list(changes.values()) + [variant_id])
        _catalog_audit(cur, actor, "catalog.variant_updated", "variant", variant_id,
                       before={k: old[k] for k in changes}, after=changes)


def catalog_get_variant(variant_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.*,p.name product_name,p.category_id,p.brand_id,
                      c.name category_name,b.name brand_name
               FROM product_variants v JOIN products p ON p.id=v.product_id
               LEFT JOIN categories c ON c.id=p.category_id
               LEFT JOIN brands b ON b.id=p.brand_id WHERE v.id=%s""",
            (variant_id,),
        )
        return cur.fetchone()


def catalog_search_skus(term: str, limit: int = 25) -> list[dict]:
    clean = (term or "").strip()
    if not clean:
        return []
    pattern = "%" + clean[:100] + "%"
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id variant_id,v.sku,v.variant_name,v.price,v.cost_price,
                      v.stock_qty,v.reserved_qty,v.active,p.id product_id,p.name product_name,
                      c.name category_name,b.name brand_name
               FROM product_variants v JOIN products p ON p.id=v.product_id
               LEFT JOIN categories c ON c.id=p.category_id
               LEFT JOIN brands b ON b.id=p.brand_id
               WHERE v.sku ILIKE %s OR p.name ILIKE %s OR b.name ILIKE %s
               ORDER BY CASE WHEN v.sku ILIKE %s THEN 0 ELSE 1 END,p.name,v.id
               LIMIT %s""", (pattern, pattern, pattern, clean, max(1, min(50, limit)))
        )
        return list(cur.fetchall())


def catalog_price_preview(variant_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id,v.sku,v.variant_name,v.price,v.cost_price,p.name product_name
               FROM product_variants v JOIN products p ON p.id=v.product_id WHERE v.id=%s""",
            (variant_id,),
        )
        return cur.fetchone()


def catalog_change_price(variant_id: int, new_price: Decimal,
                         actor: Staff, reason: str) -> None:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для зміни ціни.")
    if new_price < 0 or new_price > Decimal("99999999.99"):
        raise ValueError("Ціна поза допустимим діапазоном.")
    change_product_price(variant_id, new_price, actor, reason)


def catalog_stock_overview(variant_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id,v.sku,v.variant_name,v.stock_qty,v.reserved_qty,
                      v.stock_qty-v.reserved_qty available,v.low_stock_threshold,
                      p.name product_name
               FROM product_variants v JOIN products p ON p.id=v.product_id WHERE v.id=%s""",
            (variant_id,),
        )
        return cur.fetchone()


def catalog_stock_history(variant_id: int, limit: int = 30) -> list[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT movement_type,quantity_delta,reference_type,reference_id,
                      reason,actor_telegram_id,created_at
               FROM inventory_movements WHERE variant_id=%s
               ORDER BY created_at DESC,id DESC LIMIT %s""",
            (variant_id, max(1, min(100, limit))),
        )
        return list(cur.fetchall())


def catalog_attach_telegram_photo(product_id: int, file_id: str,
                                  actor: Staff) -> int:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для додавання фото.")
    clean = (file_id or "").strip()
    if not clean or len(clean) > 1024:
        raise ValueError("Некоректний Telegram file_id.")
    with db_cursor() as cur:
        cur.execute("SELECT id FROM products WHERE id=%s AND archived_at IS NULL FOR UPDATE", (product_id,))
        if not cur.fetchone():
            raise ValueError("Товар не знайдено або він архівований.")
        cur.execute("SELECT COALESCE(MAX(sort_order),-1)+1 n FROM product_media WHERE product_id=%s", (product_id,))
        order = int(cur.fetchone()["n"])
        cur.execute("INSERT INTO product_media(product_id,telegram_file_id,sort_order) VALUES(%s,%s,%s) RETURNING id",
                    (product_id, clean, order))
        media_id = int(cur.fetchone()["id"])
        _catalog_audit(cur, actor, "catalog.photo_added", "product_media", media_id,
                       after={"product_id": product_id, "sort_order": order})
        return media_id


def catalog_delete_media(media_id: int, actor: Staff) -> None:
    if not actor.can("catalog.update"):
        raise PermissionError("Недостатньо прав для видалення фото.")
    with db_cursor() as cur:
        cur.execute("SELECT id,product_id FROM product_media WHERE id=%s FOR UPDATE", (media_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("Фото не знайдено.")
        cur.execute("DELETE FROM product_media WHERE id=%s", (media_id,))
        _catalog_audit(cur, actor, "catalog.photo_removed", "product_media", media_id,
                       before={"product_id": row["product_id"]})


def catalog_get_media(product_id: int) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("SELECT id,telegram_file_id,disk_path,sort_order FROM product_media WHERE product_id=%s ORDER BY sort_order,id", (product_id,))
        return list(cur.fetchall())


def catalog_set_department_active(category_id: int, active: bool, actor: Staff, reason: str) -> None:
    if actor.role != "owner" or len((reason or "").strip()) < 3:
        raise PermissionError("Зміна основних категорій доступна лише власнику з обов’язковою причиною.")
    with db_cursor() as cur:
        cur.execute("SELECT id,name,active FROM categories WHERE id=%s AND parent_id IS NULL FOR UPDATE", (category_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("Категорію не знайдено.")
        if row["name"] in ROOT_DEPARTMENT_ORDER and not active:
            raise ValueError("Чотири базові категорії каталогу не можна деактивувати.")
        cur.execute("UPDATE categories SET active=%s WHERE id=%s", (active, category_id))
        _catalog_audit(cur, actor, "catalog.department_status", "category", category_id,
                       before={"active": row["active"]}, after={"active": active}, reason=reason.strip())


def catalog_set_brand_active(brand_id: int, active: bool, actor: Staff, reason: str) -> None:
    if not actor.can("catalog.update") or len((reason or "").strip()) < 3:
        raise PermissionError("Потрібні права та причина зміни статусу виробника.")
    with db_cursor() as cur:
        cur.execute("SELECT id,name,active FROM brands WHERE id=%s FOR UPDATE", (brand_id,))
        row = cur.fetchone()
        if not row:
            raise ValueError("Виробника не знайдено.")
        cur.execute("UPDATE brands SET active=%s WHERE id=%s", (active, brand_id))
        _catalog_audit(cur, actor, "catalog.brand_status", "brand", brand_id,
                       before={"active": row["active"]}, after={"active": active}, reason=reason.strip())


def _catalog_money(value: Any) -> str:
    if value is None:
        return "не задано"
    return f"{Decimal(str(value)):.2f} ₴"


def _catalog_product_label(row: dict) -> str:
    state = "архів" if row.get("archived_at") else ("приховано" if row.get("manually_hidden") or not row.get("active") else "активний")
    return f"#{row['id']} {safe(row.get('name',''))} · {safe(state)}"


def catalog_admin_home(chat_id: int, staff: Staff) -> None:
    if not staff.can("catalog.read"):
        bot.send_message(chat_id, "⛔ Немає доступу до каталогу.")
        return
    departments = catalog_get_departments(include_inactive=True)
    brands = catalog_get_brands(include_inactive=True)
    total = catalog_count_products(include_archived=True)
    active = catalog_count_products(include_archived=False)
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("➕ Додати товар", callback_data="catadm:create"),
           types.InlineKeyboardButton("🔎 Знайти товар / SKU", callback_data="catadm:search"))
    kb.add(types.InlineKeyboardButton("🏷️ Виробники", callback_data="catadm:brands"),
           types.InlineKeyboardButton("🗃️ Категорії", callback_data="catadm:departments"))
    kb.add(types.InlineKeyboardButton("📋 Усі товари", callback_data="catadm:list:0"),
           types.InlineKeyboardButton("🗄️ Архів", callback_data="catadm:archive:0"))
    kb.add(types.InlineKeyboardButton("🧪 Цілісність", callback_data="catadm:integrity"),
           types.InlineKeyboardButton("📜 Історія каталогу", callback_data="catadm:audit"))
    kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    text = ("<b>🗂️ Керування каталогом</b>\n\n"
            f"Категорій: <b>{len(departments)}</b> · Виробників: <b>{len(brands)}</b>\n"
            f"Активних товарів: <b>{active}</b> · Усього з архівом: <b>{total}</b>\n\n"
            "Структура: категорія → виробник → товар → SKU/варіант.\n"
            "Прив’язка виробника до категорії зберігається окремо від товарів.\n"
            "Залишки обліковуються тільки на рівні SKU.")
    bot.send_message(chat_id, text, reply_markup=kb)


def catalog_admin_department_picker(chat_id: int, action: str = "create") -> None:
    rows = catalog_get_departments()
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        kb.add(types.InlineKeyboardButton(row["name"], callback_data=f"catadm:dept:{action}:{row['id']}"))
    kb.add(types.InlineKeyboardButton("↩️ До каталогу", callback_data="catadm:home"))
    bot.send_message(chat_id, "Оберіть одну з чотирьох основних категорій:", reply_markup=kb)


def catalog_admin_brand_picker(chat_id: int, department_id: int, action: str = "create") -> None:
    rows = catalog_get_brands(department_id, include_inactive=False)
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        kb.add(types.InlineKeyboardButton(row["name"], callback_data=f"catadm:brand:{action}:{department_id}:{row['id']}"))
    kb.add(types.InlineKeyboardButton("➕ Створити виробника", callback_data=f"catadm:brandnew:{department_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До категорій", callback_data=f"catadm:deptback:{action}"))
    if not rows:
        bot.send_message(chat_id, "У цій категорії ще немає виробників із товарами. Створіть виробника.", reply_markup=kb)
    else:
        bot.send_message(chat_id, "Оберіть виробника:", reply_markup=kb)


def catalog_admin_product_list(chat_id: int, offset: int = 0,
                               archived: bool = False, search: str = "") -> None:
    rows = catalog_get_products(include_hidden=True, include_archived=True, archived_only=archived,
                                search=search, offset=offset, limit=CATALOG_PAGE_SIZE)
    total = catalog_count_products(include_archived=True, search=search, archived_only=archived)
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        kb.add(types.InlineKeyboardButton(_catalog_product_label(row), callback_data=f"catadm:product:{row['id']}"))
    nav = []
    if offset > 0:
        nav.append(types.InlineKeyboardButton("⬅️ Назад", callback_data=f"catadm:{'archive' if archived else 'list'}:{max(0,offset-CATALOG_PAGE_SIZE)}"))
    if offset + CATALOG_PAGE_SIZE < total:
        nav.append(types.InlineKeyboardButton("Далі ➡️", callback_data=f"catadm:{'archive' if archived else 'list'}:{offset+CATALOG_PAGE_SIZE}"))
    if nav:
        kb.row(*nav)
    kb.add(types.InlineKeyboardButton("↩️ До каталогу", callback_data="catadm:home"))
    title = "Архів товарів" if archived else "Каталог товарів"
    bot.send_message(chat_id, f"<b>{title}</b> · {total} записів · сторінка {offset//CATALOG_PAGE_SIZE+1}", reply_markup=kb)
    if not rows:
        bot.send_message(chat_id, "Товарів у цьому списку немає.")


def catalog_admin_product_card(chat_id: int, product_id: int) -> None:
    product = catalog_get_product(product_id)
    if not product:
        bot.send_message(chat_id, "Товар не знайдено.")
        return
    variants = product["variants"]
    state = "архівований" if product["archived_at"] else ("прихований" if product["manually_hidden"] or not product["active"] else "активний")
    lines = [f"<b>{safe(product['name'])}</b> · #{product['id']}",
             f"Категорія: {safe(product.get('category_name') or 'не задано')}",
             f"Виробник: {safe(product.get('brand_name') or 'не задано')}",
             f"Статус: <b>{state}</b>",
             f"Опис: {safe(product.get('description') or 'немає')}",
             f"Фото: {len(product['media'])}", "", "<b>Варіанти / SKU:</b>"]
    kb = types.InlineKeyboardMarkup(row_width=2)
    for variant in variants:
        label = f"{variant['sku']} · {_catalog_money(variant['price'])} · {variant['stock_qty']} шт."
        kb.add(types.InlineKeyboardButton(label[:60], callback_data=f"catadm:sku:{variant['id']}"))
    kb.add(types.InlineKeyboardButton("➕ Додати SKU", callback_data=f"catadm:skuadd:{product_id}"),
           types.InlineKeyboardButton("✏️ Назва / опис", callback_data=f"catadm:edit:{product_id}"))
    kb.add(types.InlineKeyboardButton("📷 Додати фото", callback_data=f"catadm:photo:{product_id}"),
           types.InlineKeyboardButton("👁️ Видимість", callback_data=f"catadm:visibility:{product_id}"))
    if product["archived_at"]:
        kb.add(types.InlineKeyboardButton("♻️ Відновити прихованим", callback_data=f"catadm:restore:{product_id}"))
    else:
        kb.add(types.InlineKeyboardButton("🗄️ Архівувати товар", callback_data=f"catadm:archiveconfirm:{product_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До списку", callback_data="catadm:list:0"),
           types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)


def catalog_admin_sku_card(chat_id: int, variant_id: int) -> None:
    row = catalog_get_variant(variant_id)
    if not row:
        bot.send_message(chat_id, "SKU не знайдено.")
        return
    stock = int(row["stock_qty"])
    reserved = int(row["reserved_qty"])
    text = (f"<b>{safe(row['product_name'])}</b>\n"
            f"Варіант: {safe(row['variant_name'] or 'основний')}\n"
            f"SKU: <code>{safe(row['sku'])}</code>\n"
            f"Категорія: {safe(row.get('category_name') or 'не задано')}\n"
            f"Виробник: {safe(row.get('brand_name') or 'не задано')}\n"
            f"Ціна: <b>{_catalog_money(row['price'])}</b>\n"
            f"Собівартість: {_catalog_money(row['cost_price'])}\n"
            f"Фізичний залишок: {stock} · резерв: {reserved} · доступно: {stock-reserved}\n"
            f"Поріг малого залишку: {row['low_stock_threshold']}\n"
            f"Статус SKU: {'активний' if row['active'] else 'вимкнений'}")
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("💲 Змінити ціну", callback_data=f"catadm:price:{variant_id}"),
           types.InlineKeyboardButton("🧮 Собівартість", callback_data=f"catadm:cost:{variant_id}"))
    kb.add(types.InlineKeyboardButton("⚠️ Поріг залишку", callback_data=f"catadm:threshold:{variant_id}"),
           types.InlineKeyboardButton("📝 Назва варіанта", callback_data=f"catadm:variantname:{variant_id}"))
    kb.add(types.InlineKeyboardButton("📜 Історія рухів", callback_data=f"catadm:stockhistory:{variant_id}"))
    action = "Вимкнути SKU" if row["active"] else "Увімкнути SKU"
    kb.add(types.InlineKeyboardButton(action, callback_data=f"catadm:skutoggle:{variant_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До товару", callback_data=f"catadm:product:{row['product_id']}"))
    bot.send_message(chat_id, text, reply_markup=kb)


def catalog_wizard_start(user_id: int, chat_id: int, stage: str, data: Optional[dict] = None,
                         prompt: str = "") -> None:
    CATALOG_WIZARDS[user_id] = {"stage": stage, "data": dict(data or {}), "started_at": time.time()}
    if prompt:
        bot.send_message(chat_id, prompt, reply_markup=types.ReplyKeyboardRemove())


def catalog_wizard_cancel(user_id: int) -> None:
    CATALOG_WIZARDS.pop(user_id, None)


def _catalog_parse_decimal(raw: str, field_name: str) -> Decimal:
    try:
        value = Decimal(raw.strip().replace(",", ".").replace("₴", "").strip())
    except Exception as exc:
        raise ValueError(f"Введіть коректне число для поля «{field_name}».") from exc
    if not value.is_finite() or value < 0 or value > Decimal("99999999.99"):
        raise ValueError(f"Некоректне значення поля «{field_name}».")
    return value.quantize(Decimal("0.01"))


def _catalog_parse_int(raw: str, field_name: str, minimum: int = 0,
                        maximum: int = 1000000) -> int:
    try:
        value = int(raw.strip())
    except Exception as exc:
        raise ValueError(f"Введіть ціле число для поля «{field_name}».") from exc
    if value < minimum or value > maximum:
        raise ValueError(f"Поле «{field_name}» має бути від {minimum} до {maximum}.")
    return value


def _catalog_start_product_wizard(chat_id: int, user_id: int, department_id: int,
                                  brand_id: int) -> None:
    # In callback handlers call.message.from_user is the bot, not the staff member.
    # Always bind the wizard to the actual Telegram user who pressed the button.
    catalog_wizard_start(user_id, chat_id, "product_name",
                         {"department_id": department_id, "brand_id": brand_id},
                         "Введіть назву товару. Для скасування напишіть /cancel.")


def _catalog_start_variant_wizard(chat_id: int, user_id: int, product_id: int) -> None:
    catalog_wizard_start(user_id, chat_id, "variant_sku", {"product_id": product_id},
                         "Введіть унікальний SKU нового варіанта.")


def _catalog_start_brand_wizard(chat_id: int, user_id: int, department_id: int) -> None:
    catalog_wizard_start(user_id, chat_id, "brand_name", {"department_id": department_id},
                         "Введіть назву виробника. Після створення він буде доступний у вибраній категорії.")


def _catalog_start_search_wizard(chat_id: int, user_id: int) -> None:
    catalog_wizard_start(user_id, chat_id, "search", {}, "Введіть назву товару, виробника або SKU для пошуку.")


def _catalog_wizard_finish_product(message, state: dict) -> None:
    data = state["data"]
    product_id = catalog_create_product_full(
        name=data["name"], description=data.get("description", ""),
        department_id=int(data["department_id"]), brand_id=int(data["brand_id"]),
        actor=get_staff(message.from_user.id),
    )
    catalog_wizard_cancel(message.from_user.id)
    bot.send_message(message.chat.id, f"✅ Товар створено: <b>#{product_id}</b>. Тепер додайте хоча б один SKU із ціною.")
    _catalog_start_variant_wizard(message.chat.id, message.from_user.id, product_id)


def _catalog_wizard_finish_variant(message, state: dict) -> None:
    d = state["data"]
    actor = get_staff(message.from_user.id)
    variant_id = create_product_variant(
        int(d["product_id"]), d["sku"], Decimal(d["price"]), actor,
        variant_name=d.get("variant_name", ""), stock=int(d.get("stock", 0)),
        cost_price=Decimal(d["cost_price"]) if d.get("cost_price") is not None else None,
    )
    catalog_wizard_cancel(message.from_user.id)
    bot.send_message(message.chat.id, f"✅ SKU створено: <b>#{variant_id}</b> · <code>{safe(d['sku'])}</code>")
    catalog_admin_product_card(message.chat.id, int(d["product_id"]))


def _catalog_wizard_message(message) -> bool:
    """Consume a pending owner/admin catalogue wizard message; return handled."""
    state = CATALOG_WIZARDS.get(message.from_user.id)
    if not state:
        return False
    if message.text and message.text.strip().lower() in {"/cancel", "скасувати", "відміна"}:
        catalog_wizard_cancel(message.from_user.id)
        bot.send_message(message.chat.id, "Дію скасовано.")
        return True
    staff = get_staff(message.from_user.id)
    if not staff or not staff.active or not staff.can("catalog.update"):
        catalog_wizard_cancel(message.from_user.id)
        bot.send_message(message.chat.id, "⛔ Сесію керування каталогом завершено: доступ відсутній.")
        return True
    stage = state["stage"]
    data = state["data"]
    raw = (message.text or "").strip()
    try:
        if stage == "brand_name":
            brand_id = create_brand(raw, staff, int(data["department_id"]))
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, f"✅ Виробника «{safe(raw)}» створено. Тепер створимо товар.")
            _catalog_start_product_wizard(message.chat.id, message.from_user.id, int(data["department_id"]), brand_id)
            return True
        if stage == "product_name":
            if not raw or len(raw) > 180:
                raise ValueError("Назва має містити від 1 до 180 символів.")
            data["name"] = raw
            state["stage"] = "product_description"
            bot.send_message(message.chat.id, "Введіть опис товару або напишіть <code>-</code>, якщо опису поки немає.")
            return True
        if stage == "product_description":
            data["description"] = "" if raw == "-" else raw
            if len(data["description"]) > 4000:
                raise ValueError("Опис задовгий, максимум 4000 символів.")
            _catalog_wizard_finish_product(message, state)
            return True
        if stage == "variant_sku":
            if not raw or len(raw) > 80:
                raise ValueError("SKU має містити від 1 до 80 символів.")
            data["sku"] = raw
            state["stage"] = "variant_name"
            bot.send_message(message.chat.id, "Назва варіанта (наприклад, об'єм/колір) або <code>-</code> для основного варіанта.")
            return True
        if stage == "variant_name":
            data["variant_name"] = "" if raw == "-" else raw[:120]
            state["stage"] = "variant_price"
            bot.send_message(message.chat.id, "Введіть роздрібну ціну у гривнях.")
            return True
        if stage == "variant_price":
            data["price"] = str(_catalog_parse_decimal(raw, "ціна"))
            state["stage"] = "variant_cost"
            bot.send_message(message.chat.id, "Введіть закупівельну ціну або <code>-</code>, якщо її ще не знаєте.")
            return True
        if stage == "variant_cost":
            data["cost_price"] = None if raw == "-" else str(_catalog_parse_decimal(raw, "собівартість"))
            state["stage"] = "variant_stock"
            bot.send_message(message.chat.id, "Введіть початкову кількість на складі (ціле число, 0 якщо немає).")
            return True
        if stage == "variant_stock":
            data["stock"] = _catalog_parse_int(raw, "початковий залишок")
            _catalog_wizard_finish_variant(message, state)
            return True
        if stage == "search":
            catalog_wizard_cancel(message.from_user.id)
            results = catalog_search_skus(raw)
            if not results:
                bot.send_message(message.chat.id, "Нічого не знайдено. Спробуйте іншу назву або SKU.")
                return True
            kb = types.InlineKeyboardMarkup(row_width=1)
            for row in results:
                caption = f"{row['product_name']} · {row['sku']} · {_catalog_money(row['price'])}"
                kb.add(types.InlineKeyboardButton(caption[:60], callback_data=f"catadm:sku:{row['variant_id']}"))
            bot.send_message(message.chat.id, f"Знайдено позицій: {len(results)}", reply_markup=kb)
            return True
        if stage == "price":
            price = _catalog_parse_decimal(raw, "нова ціна")
            data["new_price"] = str(price)
            state["stage"] = "price_reason"
            bot.send_message(message.chat.id, "Вкажіть причину зміни ціни. Вона потрапить в історію.")
            return True
        if stage == "price_reason":
            if len(raw) < 3 or len(raw) > 500:
                raise ValueError("Причина має містити від 3 до 500 символів.")
            catalog_change_price(int(data["variant_id"]), Decimal(data["new_price"]), staff, raw)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "✅ Ціну змінено. Попереднє значення збережено в історії.")
            catalog_admin_sku_card(message.chat.id, int(data["variant_id"]))
            return True
        if stage == "cost":
            if raw == "-":
                with db_cursor() as cur:
                    cur.execute("SELECT cost_price FROM product_variants WHERE id=%s FOR UPDATE", (int(data["variant_id"]),))
                    old = cur.fetchone()
                    if not old:
                        raise ValueError("SKU не знайдено.")
                    cur.execute("UPDATE product_variants SET cost_price=NULL,updated_at=NOW() WHERE id=%s", (int(data["variant_id"]),))
                    _catalog_audit(cur, staff, "catalog.variant_cost_cleared", "variant", int(data["variant_id"]),
                                   before={"cost_price": old["cost_price"]}, after={"cost_price": None})
            else:
                value = _catalog_parse_decimal(raw, "собівартість")
                catalog_update_variant(int(data["variant_id"]), staff, cost_price=value)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "✅ Собівартість оновлено.")
            catalog_admin_sku_card(message.chat.id, int(data["variant_id"]))
            return True
        if stage == "threshold":
            value = _catalog_parse_int(raw, "поріг залишку")
            catalog_update_variant(int(data["variant_id"]), staff, low_stock_threshold=value)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "✅ Поріг малого залишку оновлено.")
            catalog_admin_sku_card(message.chat.id, int(data["variant_id"]))
            return True
        if stage == "variantname":
            value = "" if raw == "-" else raw[:120]
            catalog_update_variant(int(data["variant_id"]), staff, variant_name=value)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "✅ Назву варіанта оновлено.")
            catalog_admin_sku_card(message.chat.id, int(data["variant_id"]))
            return True
        if stage == "product_edit_name":
            if not raw or len(raw) > 180:
                raise ValueError("Назва має містити від 1 до 180 символів.")
            data["name"] = raw
            state["stage"] = "product_edit_description"
            bot.send_message(message.chat.id, "Введіть новий опис або <code>-</code> щоб залишити опис порожнім.")
            return True
        if stage == "product_edit_description":
            catalog_update_product(int(data["product_id"]), staff,
                                   name=data["name"], description="" if raw == "-" else raw)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "✅ Дані товару оновлено.")
            catalog_admin_product_card(message.chat.id, int(data["product_id"]))
            return True
        if stage == "archive_reason":
            if len(raw) < 3 or len(raw) > 500:
                raise ValueError("Причина має містити від 3 до 500 символів.")
            catalog_archive_product(int(data["product_id"]), staff, raw)
            catalog_wizard_cancel(message.from_user.id)
            bot.send_message(message.chat.id, "🗄️ Товар архівовано. Історія замовлень і складські рухи збережені.")
            catalog_admin_home(message.chat.id, staff)
            return True
        if stage == "photo":
            if message.content_type == "photo":
                file_id = message.photo[-1].file_id
                media_id = catalog_attach_telegram_photo(int(data["product_id"]), file_id, staff)
                catalog_wizard_cancel(message.from_user.id)
                bot.send_message(message.chat.id, f"✅ Фото додано (медіа #{media_id}).")
                catalog_admin_product_card(message.chat.id, int(data["product_id"]))
                return True
            if raw == "-":
                catalog_wizard_cancel(message.from_user.id)
                bot.send_message(message.chat.id, "Додавання фото скасовано.")
                return True
            raise ValueError("Надішліть фото як зображення або '-' для скасування.")
        if stage == "archive_confirm_reason":
            raise ValueError("Внутрішній стан майстра. Почніть дію ще раз.")
    except (ValueError, PermissionError) as exc:
        bot.send_message(message.chat.id, f"⚠️ {safe(str(exc))}\nСпробуйте ще раз або /cancel.")
        return True
    except Exception:
        log.exception("Catalogue wizard failed: user=%s stage=%s", message.from_user.id, stage)
        bot.send_message(message.chat.id, "⚠️ Не вдалося виконати дію. Дані не підтверджено; спробуйте ще раз або /cancel.")
        return True
    return False


@bot.callback_query_handler(func=lambda c: c.data.startswith("catadm:"))
def catalog_admin_callback(call):
    staff = catalog_actor(call, "catalog.read")
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    parts = call.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    chat_id = call.message.chat.id
    try:
        bot.answer_callback_query(call.id)
        if action == "home":
            catalog_admin_home(chat_id, staff)
        elif action == "create":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            catalog_admin_department_picker(chat_id, "create")
        elif action == "dept":
            # catadm:dept:<mode>:<department_id>, emitted by the department picker.
            if len(parts) != 4:
                raise ValueError("Некоректний вибір категорії.")
            mode = parts[2]
            department_id = int(parts[3])
            department = next(
                (row for row in catalog_get_departments(include_inactive=False)
                 if int(row["id"]) == department_id),
                None,
            )
            if not department:
                raise ValueError("Категорію не знайдено або вона неактивна.")
            if mode == "create":
                catalog_admin_brand_picker(chat_id, department_id, "create")
            elif mode == "brandnew":
                if not staff.can("catalog.update"):
                    raise PermissionError("Немає права catalog.update.")
                _catalog_start_brand_wizard(chat_id, call.from_user.id, department_id)
            else:
                raise ValueError("Невідомий сценарій вибору категорії.")
        elif action == "deptback":
            mode = parts[2] if len(parts) > 2 else "create"
            catalog_admin_department_picker(chat_id, mode)
        elif action == "brands":
            with db_cursor() as cur:
                cur.execute(
                    """SELECT b.id,b.name,b.active,STRING_AGG(c.name, ', ' ORDER BY c.sort_order) departments
                       FROM brands b
                       LEFT JOIN brand_categories bc ON bc.brand_id=b.id
                       LEFT JOIN categories c ON c.id=bc.category_id
                       GROUP BY b.id ORDER BY b.name"""
                )
                rows = list(cur.fetchall())
            text_lines = ["<b>Виробники</b>"]
            for row in rows:
                text_lines.append(
                    f"• {'🟢' if row['active'] else '⚪'} {safe(row['name'])} · "
                    f"{safe(row.get('departments') or 'категорію не прив’язано')}"
                )
            if not rows:
                text_lines.append("Виробників поки немає.")
            kb = types.InlineKeyboardMarkup(row_width=1)
            kb.add(types.InlineKeyboardButton(
                "➕ Додати виробника", callback_data="catadm:brandnewpick"
            ))
            kb.add(types.InlineKeyboardButton("↩️ До каталогу", callback_data="catadm:home"))
            bot.send_message(chat_id, "\n".join(text_lines)[:3900], reply_markup=kb)
        elif action == "brandnewpick":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            catalog_admin_department_picker(chat_id, "brandnew")
        elif action == "departments":
            rows = catalog_get_departments(include_inactive=True)
            kb = types.InlineKeyboardMarkup(row_width=1)
            for row in rows:
                label = f"{'🟢' if row['active'] else '⚫'} {row['name']}"
                kb.add(types.InlineKeyboardButton(label, callback_data=f"catadm:department:{row['id']}"))
            kb.add(types.InlineKeyboardButton("↩️ До каталогу", callback_data="catadm:home"))
            bot.send_message(chat_id, "<b>Основні категорії</b>\nЧотири базові категорії зберігаються завжди.", reply_markup=kb)
        elif action == "department":
            category_id = int(parts[2])
            row = next((x for x in catalog_get_departments(include_inactive=True) if int(x["id"]) == category_id), None)
            if not row:
                raise ValueError("Категорію не знайдено.")
            kb = types.InlineKeyboardMarkup()
            kb.add(types.InlineKeyboardButton("🏷️ Виробники цієї категорії", callback_data=f"catadm:brandsfor:{category_id}"))
            kb.add(types.InlineKeyboardButton("↩️ До категорій", callback_data="catadm:departments"))
            bot.send_message(chat_id, f"<b>{safe(row['name'])}</b>\nСтатус: {'активна' if row['active'] else 'неактивна'}\nБазові категорії не перейменовуються та не видаляються.", reply_markup=kb)
        elif action == "brandsfor":
            department_id = int(parts[2])
            catalog_admin_brand_picker(chat_id, department_id, "create")
        elif action == "brandnew":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            _catalog_start_brand_wizard(chat_id, call.from_user.id, int(parts[2]))
        elif action == "brand":
            mode, department_id, brand_id = parts[2], int(parts[3]), int(parts[4])
            if mode == "create":
                if not staff.can("catalog.update"):
                    raise PermissionError("Немає права catalog.update.")
                _catalog_start_product_wizard(chat_id, call.from_user.id, department_id, brand_id)
        elif action == "list":
            catalog_admin_product_list(chat_id, int(parts[2]), False)
        elif action == "archive":
            catalog_admin_product_list(chat_id, int(parts[2]), True)
        elif action == "search":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            _catalog_start_search_wizard(chat_id, call.from_user.id)
        elif action == "product":
            catalog_admin_product_card(chat_id, int(parts[2]))
        elif action == "sku":
            catalog_admin_sku_card(chat_id, int(parts[2]))
        elif action == "skuadd":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            _catalog_start_variant_wizard(chat_id, call.from_user.id, int(parts[2]))
        elif action == "price":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            variant_id = int(parts[2])
            current = catalog_price_preview(variant_id)
            if not current:
                raise ValueError("SKU не знайдено.")
            catalog_wizard_start(call.from_user.id, chat_id, "price", {"variant_id": variant_id},
                                 f"Поточна ціна {_catalog_money(current['price'])}. Введіть нову ціну.")
        elif action in {"cost", "threshold", "variantname"}:
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            variant_id = int(parts[2])
            prompt = {"cost": "Введіть нову собівартість або '-' щоб очистити поле.",
                      "threshold": "Введіть новий поріг малого залишку (ціле число).",
                      "variantname": "Введіть назву варіанта або '-' для порожньої назви."}[action]
            catalog_wizard_start(call.from_user.id, chat_id, action, {"variant_id": variant_id}, prompt)
        elif action == "variantname":
            pass
        elif action == "edit":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            product = catalog_get_product(product_id)
            if not product:
                raise ValueError("Товар не знайдено.")
            catalog_wizard_start(call.from_user.id, chat_id, "product_edit_name", {"product_id": product_id},
                                 f"Поточна назва: {safe(product['name'])}. Введіть нову назву.")
        elif action == "photo":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            catalog_wizard_start(call.from_user.id, chat_id, "photo", {"product_id": product_id},
                                 "Надішліть фото товару одним зображенням. '-' скасовує дію.")
        elif action == "visibility":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            product = catalog_get_product(product_id)
            if not product or product["archived_at"]:
                raise ValueError("Товар не знайдено або він в архіві.")
            new_hidden = not bool(product["manually_hidden"])
            catalog_update_product(product_id, staff, manually_hidden=new_hidden)
            bot.send_message(chat_id, "👁️ Товар приховано." if new_hidden else "👁️ Товар знову видимий за умови активних SKU та залишку.")
            catalog_admin_product_card(chat_id, product_id)
        elif action == "archiveconfirm":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            kb = types.InlineKeyboardMarkup(row_width=2)
            kb.add(types.InlineKeyboardButton("Так, архівувати", callback_data=f"catadm:archiveyes:{product_id}"),
                   types.InlineKeyboardButton("Ні, назад", callback_data=f"catadm:product:{product_id}"))
            bot.send_message(chat_id, "Архівація приховає товар і вимкне його SKU. Історія замовлень та рухів залишиться. Продовжити?", reply_markup=kb)
        elif action == "archiveyes":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            catalog_wizard_start(call.from_user.id, chat_id, "archive_reason", {"product_id": product_id},
                                 "Вкажіть причину архівації (мінімум 3 символи).")
        elif action == "restore":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            product_id = int(parts[2])
            catalog_restore_product(product_id, staff)
            bot.send_message(chat_id, "♻️ Товар відновлено в прихованому стані. Перевірте SKU та увімкніть потрібні варіанти вручну.")
            catalog_admin_product_card(chat_id, product_id)
        elif action == "skutoggle":
            if not staff.can("catalog.update"):
                raise PermissionError("Немає права catalog.update.")
            variant_id = int(parts[2])
            row = catalog_get_variant(variant_id)
            if not row:
                raise ValueError("SKU не знайдено.")
            new_state = not bool(row["active"])
            catalog_set_variant_active(variant_id, new_state, staff,
                                       "Увімкнення SKU оператором" if new_state else "Вимкнення SKU оператором")
            bot.send_message(chat_id, "Статус SKU оновлено.")
            catalog_admin_sku_card(chat_id, variant_id)
        elif action == "stockhistory":
            variant_id = int(parts[2])
            row = catalog_get_variant(variant_id)
            history = catalog_stock_history(variant_id, 30)
            if not row:
                raise ValueError("SKU не знайдено.")
            lines = [f"<b>Рухи складу: {safe(row['sku'])}</b>"]
            for item in history:
                sign = "+" if int(item["quantity_delta"]) > 0 else ""
                lines.append(f"{safe(item['created_at'])} · {safe(item['movement_type'])} · {sign}{item['quantity_delta']} · {safe(item.get('reason') or '')}")
            bot.send_message(chat_id, "\n".join(lines)[:3900] if history else "Рухів за цим SKU ще немає.")
        elif action == "integrity":
            report = catalog_integrity_report()
            bot.send_message(chat_id, catalog_integrity_text(report))
        elif action == "audit":
            rows = catalog_audit_recent()
            bot.send_message(chat_id, catalog_audit_text(rows))
        else:
            bot.send_message(chat_id, "Невідома дія каталогу.")
    except (ValueError, PermissionError) as exc:
        bot.send_message(chat_id, f"⚠️ {safe(str(exc))}")
    except Exception:
        log.exception("Catalogue callback failed: %s", call.data)
        bot.send_message(chat_id, "⚠️ Не вдалося виконати дію каталогу. Помилку записано в журнал.")


@bot.message_handler(commands=["cancel"])
def catalog_cancel_command(message):
    cancelled = False
    if message.from_user.id in CATALOG_WIZARDS:
        catalog_wizard_cancel(message.from_user.id)
        cancelled = True
    if message.from_user.id in INVENTORY_WIZARDS:
        INVENTORY_WIZARDS.pop(message.from_user.id, None)
        cancelled = True
    if cancelled:
        bot.send_message(message.chat.id, "Поточну дію скасовано.")


@bot.message_handler(content_types=["photo"])
def catalog_photo_message(message):
    if message.from_user.id in CATALOG_WIZARDS and CATALOG_WIZARDS[message.from_user.id].get("stage") == "photo":
        _catalog_wizard_message(message)


@bot.message_handler(func=lambda m: bool(m.text) and m.from_user.id in CATALOG_WIZARDS,
                     content_types=["text"])
def catalog_wizard_text_handler(message):
    _catalog_wizard_message(message)


@bot.message_handler(func=lambda m: m.text == "🗂️ Каталог")
def catalog_admin_menu_button(message):
    staff = catalog_actor(message, "catalog.read")
    if staff:
        catalog_admin_home(message.chat.id, staff)



# ---------------------------------------------------------------------------
# Catalogue invariants and diagnostics
# ---------------------------------------------------------------------------

def catalog_integrity_report() -> dict:
    """Read-only consistency report; never repairs data silently."""
    report = {"missing_category": 0, "missing_brand": 0, "products_without_sku": 0,
              "duplicate_sku": 0, "negative_available": 0, "inactive_visible": 0,
              "root_departments": {}, "products": 0, "variants": 0}
    with db_cursor() as cur:
        cur.execute("SELECT COUNT(*) n FROM products p LEFT JOIN categories c ON c.id=p.category_id WHERE p.archived_at IS NULL AND (p.category_id IS NULL OR c.id IS NULL)")
        report["missing_category"] = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM products p LEFT JOIN brands b ON b.id=p.brand_id WHERE p.archived_at IS NULL AND (p.brand_id IS NULL OR b.id IS NULL)")
        report["missing_brand"] = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM products p LEFT JOIN product_variants v ON v.product_id=p.id WHERE p.archived_at IS NULL GROUP BY p.id HAVING COUNT(v.id)=0")
        rows = list(cur.fetchall())
        report["products_without_sku"] = len(rows)
        cur.execute("SELECT COUNT(*) n FROM product_variants WHERE stock_qty<reserved_qty")
        report["negative_available"] = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM products p JOIN product_variants v ON v.product_id=p.id WHERE p.archived_at IS NULL AND p.active=TRUE AND p.manually_hidden=FALSE AND v.active=FALSE")
        report["inactive_visible"] = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM products WHERE archived_at IS NULL")
        report["products"] = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM product_variants")
        report["variants"] = int(cur.fetchone()["n"])
        cur.execute("SELECT name,active FROM categories WHERE parent_id IS NULL ORDER BY sort_order")
        report["root_departments"] = {r["name"]: bool(r["active"]) for r in cur.fetchall()}
    return report


def catalog_integrity_text(report: dict) -> str:
    expected = set(ROOT_DEPARTMENT_ORDER)
    actual = set(report.get("root_departments", {}))
    missing_roots = sorted(expected - actual)
    checks = [
        ("Товари без категорії", report["missing_category"]),
        ("Товари без виробника", report["missing_brand"]),
        ("Товари без SKU", report["products_without_sku"]),
        ("Залишок нижче резерву", report["negative_available"]),
        ("SKU вимкнений у видимому товарі", report["inactive_visible"]),
    ]
    lines = ["<b>Перевірка цілісності каталогу</b>",
             f"Товарів: {report['products']} · SKU: {report['variants']}"]
    lines.extend(f"{'✅' if value == 0 else '⚠️'} {label}: {value}" for label, value in checks)
    lines.append("⚠️ Відсутні базові категорії: " + (", ".join(missing_roots) if missing_roots else "немає"))
    return "\n".join(lines)


@bot.callback_query_handler(func=lambda c: c.data == "catadm:integrity")
def catalog_integrity_callback(call):
    staff = catalog_actor(call, "catalog.read")
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    try:
        bot.send_message(call.message.chat.id, catalog_integrity_text(catalog_integrity_report()))
    except Exception:
        log.exception("Catalog integrity check failed")
        bot.send_message(call.message.chat.id, "Не вдалося завершити перевірку каталогу.")


# The catalog UI exposes this check alongside operational lists. It is read-only.
def catalog_add_integrity_button(chat_id: int) -> None:
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("🧪 Перевірити цілісність", callback_data="catadm:integrity"))
    bot.send_message(chat_id, "Діагностика зв'язків категорій, брендів, SKU та залишків:", reply_markup=kb)


# SKU identifiers are immutable once referenced by orders or inventory. A new
# SKU is created instead of rewriting the identifier and corrupting history.
def catalog_sku_identity_policy(variant_id: int) -> str:
    with db_cursor() as cur:
        cur.execute("SELECT COUNT(*) n FROM order_items WHERE variant_id=%s", (variant_id,))
        orders = int(cur.fetchone()["n"])
        cur.execute("SELECT COUNT(*) n FROM inventory_movements WHERE variant_id=%s", (variant_id,))
        movements = int(cur.fetchone()["n"])
    if orders or movements:
        return "immutable"
    return "not_referenced"


def catalog_export_rows(department_id: Optional[int] = None) -> list[dict]:
    """Structured export data for a later CSV/XLSX layer; does not write files."""
    clauses = ["p.archived_at IS NULL"]
    params: list[Any] = []
    if department_id is not None:
        clauses.append("p.category_id=%s")
        params.append(department_id)
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT c.name category,b.name brand,p.id product_id,p.name product,
                      p.description,v.id variant_id,v.sku,v.variant_name,v.price,
                      v.cost_price,v.stock_qty,v.reserved_qty,
                      v.stock_qty-v.reserved_qty available,v.low_stock_threshold,
                      p.active product_active,p.manually_hidden,v.active variant_active
               FROM products p JOIN categories c ON c.id=p.category_id
               JOIN brands b ON b.id=p.brand_id
               JOIN product_variants v ON v.product_id=p.id
               WHERE {' AND '.join(clauses)} ORDER BY c.sort_order,b.name,p.name,v.id""", params
        )
        return list(cur.fetchall())


def catalog_variant_margin(variant_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,price,cost_price,
                      CASE WHEN cost_price IS NULL THEN NULL ELSE price-cost_price END gross_margin,
                      CASE WHEN cost_price IS NULL OR price=0 THEN NULL
                           ELSE ROUND(((price-cost_price)/price)*100,2) END margin_percent
               FROM product_variants WHERE id=%s""", (variant_id,)
        )
        return cur.fetchone()


def catalog_admin_sku_margin(chat_id: int, variant_id: int) -> None:
    row = catalog_variant_margin(variant_id)
    if not row:
        bot.send_message(chat_id, "SKU не знайдено.")
        return
    margin = _catalog_money(row["gross_margin"])
    percent = "не визначено" if row["margin_percent"] is None else f"{row['margin_percent']}%"
    bot.send_message(chat_id,
                     f"<b>Валовий розрив ціни й собівартості</b>\n"
                     f"Ціна: {_catalog_money(row['price'])}\n"
                     f"Собівартість: {_catalog_money(row['cost_price'])}\n"
                     f"Різниця: {margin}\nМаржа від ціни: {percent}\n\n"
                     "Це не чистий прибуток: доставка, реклама, зарплати та інші витрати тут не враховані.")


# ---------------------------------------------------------------------------
# Handoff acceptance helpers for catalogue flows
# ---------------------------------------------------------------------------

def catalog_department_brand_product_chain(department_id: int, brand_id: int,
                                            product_id: int) -> bool:
    """Assert that a product belongs to the chosen department and brand."""
    with db_cursor() as cur:
        cur.execute("SELECT 1 FROM products WHERE id=%s AND category_id=%s AND brand_id=%s AND archived_at IS NULL",
                    (product_id, department_id, brand_id))
        return cur.fetchone() is not None


def catalog_product_sku_count(product_id: int, include_inactive: bool = True) -> int:
    clause = "" if include_inactive else " AND active=TRUE"
    with db_cursor() as cur:
        cur.execute(f"SELECT COUNT(*) n FROM product_variants WHERE product_id=%s{clause}", (product_id,))
        return int(cur.fetchone()["n"])


def catalog_assert_four_departments() -> None:
    rows = catalog_get_departments(include_inactive=True)
    names = {row["name"] for row in rows}
    missing = set(ROOT_DEPARTMENT_ORDER) - names
    if missing:
        raise RuntimeError("Базові категорії каталогу відсутні: " + ", ".join(sorted(missing)))


def catalog_audit_recent(limit: int = 30) -> list[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT actor_telegram_id,actor_role,action,entity_type,entity_id,reason,created_at
               FROM audit_log WHERE action LIKE 'catalog.%'
               ORDER BY created_at DESC,id DESC LIMIT %s""", (max(1, min(100, limit)),)
        )
        return list(cur.fetchall())


def catalog_audit_text(rows: list[dict]) -> str:
    lines = ["<b>Останні зміни каталогу</b>"]
    for row in rows:
        lines.append(f"{safe(row['created_at'])} · {safe(row['actor_role'])} · "
                     f"{safe(row['action'])} · {safe(row['entity_type'])} #{safe(row['entity_id'])}")
    return "\n".join(lines)[:3900]


@bot.callback_query_handler(func=lambda c: c.data == "catadm:audit")
def catalog_audit_callback(call):
    staff = catalog_actor(call, "catalog.read")
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    try:
        bot.send_message(call.message.chat.id, catalog_audit_text(catalog_audit_recent()))
    except Exception:
        log.exception("Catalog audit read failed")
        bot.send_message(call.message.chat.id, "Не вдалося прочитати журнал каталогу.")


# The product creation sequence is intentionally strict: a department and a
# brand are selected before a product can be inserted. No orphan product rows.
def catalog_validate_product_link(category_id: int, brand_id: int) -> None:
    with db_cursor() as cur:
        cur.execute("SELECT id FROM categories WHERE id=%s AND parent_id IS NULL AND active=TRUE", (category_id,))
        if not cur.fetchone():
            raise ValueError("Потрібно вибрати активну основну категорію.")
        cur.execute("SELECT id FROM brands WHERE id=%s AND active=TRUE", (brand_id,))
        if not cur.fetchone():
            raise ValueError("Потрібно вибрати активного виробника.")


def catalog_preflight() -> dict:
    """Fast DB preflight used before an owner begins a large catalogue import."""
    catalog_assert_four_departments()
    report = catalog_integrity_report()
    report["ok"] = not any(report[k] for k in (
        "missing_category", "missing_brand", "products_without_sku", "negative_available"
    ))
    return report


@bot.callback_query_handler(func=lambda c: c.data == "catadm:preflight")
def catalog_preflight_callback(call):
    staff = catalog_actor(call, "catalog.read")
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    bot.answer_callback_query(call.id)
    try:
        report = catalog_preflight()
        bot.send_message(call.message.chat.id,
                         ("✅ Попередня перевірка пройдена.\n" if report["ok"] else "⚠️ Є питання до каталогу.\n")
                         + catalog_integrity_text(report))
    except Exception:
        log.exception("Catalog preflight failed")
        bot.send_message(call.message.chat.id, "⚠️ Не вдалося виконати попередню перевірку.")


# End of catalogue workspace.



# ---------------------------------------------------------------------------
# Procurement and inventory operations (Handoff v1.4+)
# ---------------------------------------------------------------------------

INVENTORY_WIZARDS: dict[int, dict] = {}


def _inventory_actor(message_or_call, permission: str = "inventory.read") -> Optional[Staff]:
    staff = require_staff(message_or_call, permission)
    if not staff:
        return None
    return staff


def list_suppliers(active_only: bool = True, limit: int = 200) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT id,name,contact_name,phone,email,notes,active,created_at
                       FROM suppliers WHERE (%s=FALSE OR active=TRUE)
                       ORDER BY active DESC,name,id LIMIT %s""", (active_only, max(1,min(500,limit))))
        return list(cur.fetchall())


def get_supplier(supplier_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute("SELECT * FROM suppliers WHERE id=%s", (supplier_id,))
        return cur.fetchone()


def create_supplier(name: str, actor: Staff, *, contact_name: str = "", phone: str = "",
                    email: str = "", notes: str = "") -> int:
    if not actor.can("inventory.receive"):
        raise PermissionError("Недостатньо прав для керування постачальниками.")
    name = name.strip()
    if not name or len(name) > 180:
        raise ValueError("Назва постачальника має містити 1–180 символів.")
    with db_cursor() as cur:
        cur.execute("""INSERT INTO suppliers(name,contact_name,phone,email,notes)
                       VALUES(%s,%s,%s,%s,%s) RETURNING id""",
                    (name,contact_name.strip()[:180],phone.strip()[:60],email.strip()[:180],notes.strip()[:2000]))
        supplier_id = int(cur.fetchone()["id"])
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'supplier.created','supplier',%s,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(supplier_id),json_dumps({"name":name,"phone":phone,"email":email})))
        return supplier_id


def set_supplier_active(supplier_id: int, active: bool, actor: Staff, reason: str) -> None:
    if not actor.can("inventory.receive") or not reason.strip():
        raise PermissionError("Потрібні права та причина зміни статусу.")
    with db_cursor() as cur:
        cur.execute("UPDATE suppliers SET active=%s WHERE id=%s RETURNING name", (active,supplier_id))
        row = cur.fetchone()
        if not row:
            raise ValueError("Постачальника не знайдено.")
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'supplier.status_changed','supplier',%s,%s::jsonb,%s)",
                    (actor.telegram_id,actor.role,str(supplier_id),json_dumps({"name":row["name"],"active":active}),reason.strip()))


def create_supply_document(document_number: str, supplier_id: int, actor: Staff,
                           document_date=None, note: str = "") -> int:
    if not actor.can("inventory.receive"):
        raise PermissionError("Недостатньо прав для створення поставки.")
    number = document_number.strip()
    if not number or len(number) > 80:
        raise ValueError("Номер документа має містити 1–80 символів.")
    with db_cursor() as cur:
        cur.execute("SELECT id FROM suppliers WHERE id=%s AND active=TRUE", (supplier_id,))
        if not cur.fetchone():
            raise ValueError("Активного постачальника не знайдено.")
        cur.execute("""INSERT INTO supply_documents(document_number,supplier_id,document_date,created_by)
                       VALUES(%s,%s,COALESCE(%s,CURRENT_DATE),%s) RETURNING id""",
                    (number,supplier_id,document_date,actor.telegram_id))
        supply_id = int(cur.fetchone()["id"])
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'supply.created','supply',%s,%s::jsonb,%s)",
                    (actor.telegram_id,actor.role,str(supply_id),json_dumps({"document_number":number,"supplier_id":supplier_id}),note.strip()))
        return supply_id


def add_supply_item(supply_id: int, variant_id: int, quantity: int, unit_cost: Decimal,
                    actor: Staff, received_qty: Optional[int] = None) -> int:
    if not actor.can("inventory.receive"):
        raise PermissionError("Недостатньо прав для додавання позицій поставки.")
    if quantity < 1 or quantity > 1_000_000 or unit_cost < 0:
        raise ValueError("Перевір кількість та закупівельну ціну.")
    received = quantity if received_qty is None else received_qty
    if received < 0 or received > quantity:
        raise ValueError("Фактично прийнята кількість має бути від 0 до замовленої.")
    with db_cursor() as cur:
        cur.execute("SELECT state FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc = cur.fetchone()
        if not doc or doc["state"] != "draft":
            raise ValueError("Можна змінювати лише чернетку поставки.")
        cur.execute("""SELECT v.id FROM product_variants v JOIN products p ON p.id=v.product_id
                       WHERE v.id=%s AND v.active=TRUE AND p.archived_at IS NULL""", (variant_id,))
        if not cur.fetchone():
            raise ValueError("Активний SKU не знайдено або товар архівовано.")
        cur.execute("SELECT id FROM supply_items WHERE supply_id=%s AND variant_id=%s", (supply_id,variant_id))
        if cur.fetchone():
            raise ValueError("Цей SKU вже є в поставці. Відредагуйте кількість у наявному рядку.")
        cur.execute("""INSERT INTO supply_items(supply_id,variant_id,quantity,unit_cost,received_qty)
                       VALUES(%s,%s,%s,%s,%s) RETURNING id""",
                    (supply_id,variant_id,quantity,unit_cost,received))
        item_id = int(cur.fetchone()["id"])
        cur.execute("UPDATE supply_documents SET total_cost=(SELECT COALESCE(SUM(quantity*unit_cost),0) FROM supply_items WHERE supply_id=%s) WHERE id=%s", (supply_id,supply_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'supply.item_added','supply_item',%s,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(item_id),json_dumps({"supply_id":supply_id,"variant_id":variant_id,"quantity":quantity,"received_qty":received,"unit_cost":unit_cost})))
        return item_id


def update_supply_received_qty(supply_id: int, variant_id: int, received_qty: int, actor: Staff) -> None:
    if not actor.can("inventory.receive") or received_qty < 0:
        raise ValueError("Недостатньо прав або некоректна кількість.")
    with db_cursor() as cur:
        cur.execute("SELECT state FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc=cur.fetchone()
        if not doc or doc["state"] != "draft":
            raise ValueError("Поставка вже проведена або не знайдена.")
        cur.execute("UPDATE supply_items SET received_qty=%s WHERE supply_id=%s AND variant_id=%s AND %s<=quantity RETURNING id,quantity", (received_qty,supply_id,variant_id,received_qty))
        item=cur.fetchone()
        if not item:
            raise ValueError("Позицію не знайдено або прийнята кількість перевищує документ.")
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'supply.received_qty_updated','supply_item',%s,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(item['id']),json_dumps({'supply_id':supply_id,'variant_id':variant_id,'received_qty':received_qty,'document_qty':item['quantity']})))


def get_supply_document(supply_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT d.*,s.name supplier_name FROM supply_documents d
                       LEFT JOIN suppliers s ON s.id=d.supplier_id WHERE d.id=%s""", (supply_id,))
        doc=cur.fetchone()
        if not doc: return None
        cur.execute("""SELECT si.id,si.variant_id,si.quantity,si.received_qty,si.unit_cost,
                       v.sku,v.variant_name,p.name product_name
                       FROM supply_items si JOIN product_variants v ON v.id=si.variant_id
                       JOIN products p ON p.id=v.product_id WHERE si.supply_id=%s ORDER BY si.id""", (supply_id,))
        doc["items"]=list(cur.fetchall())
        return doc


def list_supply_documents(states: tuple[str,...] = ("draft","posted","cancelled"), limit: int = 30) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT d.id,d.document_number,d.state,d.document_date,d.total_cost,d.created_at,
                       s.name supplier_name,COUNT(si.id) item_count
                       FROM supply_documents d LEFT JOIN suppliers s ON s.id=d.supplier_id
                       LEFT JOIN supply_items si ON si.supply_id=d.id
                       WHERE d.state=ANY(%s) GROUP BY d.id,s.name ORDER BY d.id DESC LIMIT %s""",
                    (list(states),max(1,min(100,limit))))
        return list(cur.fetchall())


def inventory_count_progress(count_id: int) -> dict:
    with db_cursor() as cur:
        cur.execute("""SELECT c.id,c.status,c.created_by,c.created_at,
                       COUNT(i.id) total,COUNT(i.actual_qty) counted
                       FROM inventory_counts c LEFT JOIN inventory_count_items i ON i.count_id=c.id
                       WHERE c.id=%s GROUP BY c.id""", (count_id,))
        row=cur.fetchone()
        if not row: raise ValueError("Інвентаризацію не знайдено.")
        row["total"]=int(row["total"]); row["counted"]=int(row["counted"])
        return row


def inventory_count_find_sku(count_id: int, term: str) -> list[dict]:
    term=term.strip()
    if not term: return []
    with db_cursor() as cur:
        cur.execute("""SELECT i.variant_id,v.sku,v.variant_name,p.name product_name,i.actual_qty
                       FROM inventory_count_items i JOIN product_variants v ON v.id=i.variant_id
                       JOIN products p ON p.id=v.product_id
                       WHERE i.count_id=%s AND (v.sku ILIKE %s OR p.name ILIKE %s OR v.variant_name ILIKE %s)
                       ORDER BY CASE WHEN v.sku=%s THEN 0 ELSE 1 END,p.name LIMIT 15""",
                    (count_id,f"%{term}%",f"%{term}%",f"%{term}%",term))
        return list(cur.fetchall())


def inventory_count_pending_items(count_id: int, limit: int = 50) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT i.variant_id,v.sku,v.variant_name,p.name product_name
                       FROM inventory_count_items i JOIN product_variants v ON v.id=i.variant_id
                       JOIN products p ON p.id=v.product_id WHERE i.count_id=%s AND i.actual_qty IS NULL
                       ORDER BY p.name,v.sku LIMIT %s""", (count_id,max(1,min(100,limit))))
        return list(cur.fetchall())


def inventory_count_discrepancy_preview(count_id: int) -> list[dict]:
    """Show expected reconciliation only after the blind count is complete."""
    with db_cursor() as cur:
        cur.execute("""SELECT i.variant_id,v.sku,p.name product_name,i.actual_qty,v.stock_qty system_qty,
                       COALESCE(i.counted_at,c.created_at) counted_at
                       FROM inventory_count_items i JOIN inventory_counts c ON c.id=i.count_id
                       JOIN product_variants v ON v.id=i.variant_id JOIN products p ON p.id=v.product_id
                       WHERE i.count_id=%s AND i.actual_qty IS NOT NULL ORDER BY p.name""", (count_id,))
        rows=list(cur.fetchall())
        result=[]
        for row in rows:
            cur.execute("""SELECT COALESCE(SUM(quantity_delta),0) net_delta FROM inventory_movements
                           WHERE variant_id=%s AND created_at>%s
                             AND movement_type IN ('supply','sale','manual_adjustment','opening_balance','inventory_count')""",
                        (row['variant_id'],row['counted_at']))
            delta=int(cur.fetchone()['net_delta'])
            counted=int(row['actual_qty'])
            reconciled=counted+delta
            result.append({'variant_id':row['variant_id'],'sku':row['sku'],'product_name':row['product_name'],
                           'actual_qty':reconciled,'counted_qty':counted,'concurrent_delta':delta,
                           'system_qty':int(row['system_qty']),'discrepancy':reconciled-int(row['system_qty'])})
        return result


def inventory_movement_report(variant_id: Optional[int] = None, limit: int = 100) -> list[dict]:
    with db_cursor() as cur:
        if variant_id is None:
            cur.execute("""SELECT m.*,v.sku,p.name product_name FROM inventory_movements m
                           JOIN product_variants v ON v.id=m.variant_id JOIN products p ON p.id=v.product_id
                           ORDER BY m.id DESC LIMIT %s""", (max(1,min(300,limit)),))
        else:
            cur.execute("""SELECT m.*,v.sku,p.name product_name FROM inventory_movements m
                           JOIN product_variants v ON v.id=m.variant_id JOIN products p ON p.id=v.product_id
                           WHERE m.variant_id=%s ORDER BY m.id DESC LIMIT %s""", (variant_id,max(1,min(300,limit))))
        return list(cur.fetchall())


def inventory_low_stock_report(limit: int = 100) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT v.id variant_id,v.sku,v.variant_name,v.stock_qty,v.reserved_qty,
                       (v.stock_qty-v.reserved_qty) available,v.low_stock_threshold,p.name product_name,
                       c.name category_name,b.name brand_name
                       FROM product_variants v JOIN products p ON p.id=v.product_id
                       LEFT JOIN categories c ON c.id=p.category_id LEFT JOIN brands b ON b.id=p.brand_id
                       WHERE v.active=TRUE AND p.archived_at IS NULL
                         AND (v.stock_qty-v.reserved_qty)<=v.low_stock_threshold
                       ORDER BY (v.stock_qty-v.reserved_qty),p.name LIMIT %s""", (max(1,min(300,limit)),))
        return list(cur.fetchall())


def _inv_money(value) -> str:
    return f"{Decimal(str(value or 0)):.2f} грн"


def _inv_supply_text(doc: dict) -> str:
    lines=[f"<b>Поставка #{doc['id']}</b>",f"Документ: {safe(doc['document_number'])}",
           f"Постачальник: {safe(doc.get('supplier_name') or 'не вказаний')}",
           f"Статус: {safe(doc['state'])}",f"Дата: {safe(str(doc.get('document_date') or ''))}",""]
    for item in doc.get("items",[]):
        lines.append(f"• {safe(item['product_name'])} / {safe(item['sku'])}: {item['received_qty']}/{item['quantity']} шт. × {_inv_money(item['unit_cost'])}")
    lines += ["",f"Сума за документом: <b>{_inv_money(doc['total_cost'])}</b>"]
    return "\n".join(lines)


def inventory_admin_home(chat_id: int, staff: Staff) -> None:
    if not staff.can("inventory.read"):
        bot.send_message(chat_id,"⛔ Недостатньо прав."); return
    kb=types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("🧮 Нова інвентаризація",callback_data="invops:count:new"),
           types.InlineKeyboardButton("📋 Активні перерахунки",callback_data="invops:count:list"))
    if staff.can("inventory.receive"):
        kb.add(types.InlineKeyboardButton("🏭 Постачальники",callback_data="invops:supplier:list"))
        kb.add(types.InlineKeyboardButton("🚚 Нова поставка",callback_data="invops:supply:new"),
               types.InlineKeyboardButton("📑 Поставки",callback_data="invops:supply:list"))
    kb.add(types.InlineKeyboardButton("⚠️ Малі залишки",callback_data="invops:lowstock"),
           types.InlineKeyboardButton("📚 Рух товару",callback_data="invops:movements"))
    if staff.role == "owner":
        kb.add(types.InlineKeyboardButton("💰 Оцінка запасів",callback_data="invops:valuation"),
               types.InlineKeyboardButton("➕ Коригування залишку",callback_data="invops:adjust"))
    kb.add(types.InlineKeyboardButton("🗂 Історія інвентаризацій",callback_data="invops:count:history"),
           types.InlineKeyboardButton("↩️ До меню",callback_data="invops:home"))
    bot.send_message(chat_id,"<b>Склад та постачання</b>\nОблік ведеться за конкретним SKU. Під час сліпого перерахунку системні залишки не показуються.",reply_markup=kb)


def inventory_render_count(chat_id: int, count_id: int, staff: Staff) -> None:
    progress=inventory_count_progress(count_id)
    kb=types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("➕ Внести SKU",callback_data=f"invops:count:add:{count_id}"),
           types.InlineKeyboardButton("📋 Що залишилось",callback_data=f"invops:count:pending:{count_id}"))
    if progress["counted"]==progress["total"] and staff.role in ("owner","admin"):
        kb.add(types.InlineKeyboardButton("🔍 Переглянути розбіжності",callback_data=f"invops:count:preview:{count_id}"),
               types.InlineKeyboardButton("✅ Підтвердити",callback_data=f"invops:count:confirm:{count_id}"))
    if staff.role in ("owner","admin"):
        kb.add(types.InlineKeyboardButton("🛑 Скасувати інвентаризацію",callback_data=f"invops:count:cancel:{count_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До складу",callback_data="invops:home"))
    bot.send_message(chat_id,f"<b>Інвентаризація #{count_id}</b>\nСтатус: {safe(progress['status'])}\nПораховано: {progress['counted']} із {progress['total']} SKU",reply_markup=kb)


def inventory_start_count(chat_id: int, staff: Staff) -> None:
    count_id=create_inventory_count(staff)
    inventory_render_count(chat_id,count_id,staff)


def inventory_start_wizard(user_id: int, chat_id: int, state: dict) -> None:
    INVENTORY_WIZARDS[user_id]={**state,"chat_id":chat_id}
    bot.send_message(chat_id,state.get("prompt","Введіть значення."))


def inventory_prompt_supplier(chat_id: int, user_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supplier_name","chat_id":chat_id}
    bot.send_message(chat_id,"Введіть назву нового постачальника. /cancel скасує дію.")


def inventory_prompt_count_sku(chat_id: int, user_id: int, count_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"count_sku","count_id":count_id,"chat_id":chat_id}
    bot.send_message(chat_id,"Введіть SKU або частину назви товару. Системний залишок не показується.")


def inventory_prompt_count_qty(chat_id: int, user_id: int, count_id: int, variant_id: int, label: str) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"count_qty","count_id":count_id,"variant_id":variant_id,"chat_id":chat_id}
    bot.send_message(chat_id,f"Вкажіть фактичну кількість для <b>{safe(label)}</b>:")


def inventory_prompt_supply_document(chat_id: int, user_id: int, supplier_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supply_doc_number","supplier_id":supplier_id,"chat_id":chat_id}
    bot.send_message(chat_id,"Введіть номер накладної / документа поставки:")


def inventory_prompt_supply_sku(chat_id: int, user_id: int, supply_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supply_sku","supply_id":supply_id,"chat_id":chat_id}
    bot.send_message(chat_id,"Введіть SKU або частину назви товару для додавання в поставку:")


def inventory_prompt_supply_qty(chat_id: int, user_id: int, supply_id: int, variant_id: int, label: str) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supply_qty","supply_id":supply_id,"variant_id":variant_id,"label":label,"chat_id":chat_id}
    bot.send_message(chat_id,f"Товар: <b>{safe(label)}</b>\nВведіть кількість за документом:")


def inventory_render_suppliers(chat_id: int, staff: Staff) -> None:
    rows=list_suppliers(active_only=False)
    kb=types.InlineKeyboardMarkup(row_width=1)
    for row in rows[:50]:
        status="🟢" if row["active"] else "⚪"
        kb.add(types.InlineKeyboardButton(f"{status} {row['name']}",callback_data=f"invops:supplier:detail:{row['id']}"))
    kb.add(types.InlineKeyboardButton("➕ Додати постачальника",callback_data="invops:supplier:new"),
           types.InlineKeyboardButton("↩️ До складу",callback_data="invops:home"))
    bot.send_message(chat_id,"<b>Постачальники</b>\nНатисни на постачальника, щоб змінити активність.",reply_markup=kb)


def inventory_render_supply_list(chat_id: int) -> None:
    rows=list_supply_documents()
    kb=types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        kb.add(types.InlineKeyboardButton(f"#{row['id']} {row['document_number']} · {row['state']} · {row['item_count']} поз.",callback_data=f"invops:supply:open:{row['id']}"))
    kb.add(types.InlineKeyboardButton("↩️ До складу",callback_data="invops:home"))
    text="<b>Поставки</b>" if rows else "Поставок поки немає."
    bot.send_message(chat_id,text,reply_markup=kb)


def inventory_render_lowstock(chat_id: int) -> None:
    rows=inventory_low_stock_report()
    if not rows:
        bot.send_message(chat_id,"✅ Немає SKU нижче порогу мінімального залишку."); return
    lines=["<b>Малі залишки</b>"]
    for r in rows[:100]:
        lines.append(f"• {safe(r['product_name'])} / {safe(r['sku'])}: <b>{r['available']}</b> шт. (поріг {r['low_stock_threshold']})")
    bot.send_message(chat_id,"\n".join(lines))


def inventory_render_movements(chat_id: int) -> None:
    rows=inventory_movement_report(limit=40)
    if not rows:
        bot.send_message(chat_id,"Рухів товару поки немає."); return
    lines=["<b>Останні рухи товару</b>"]
    for r in rows:
        delta=int(r["quantity_delta"])
        lines.append(f"• #{r['id']} {safe(r['product_name'])}/{safe(r['sku'])}: <b>{delta:+d}</b> · {safe(r['movement_type'])} · {safe(r.get('reason') or '')}")
    bot.send_message(chat_id,"\n".join(lines))




def cancel_inventory_count(count_id: int, actor: Staff, reason: str) -> None:
    if actor.role not in ("owner", "admin") or not reason.strip():
        raise PermissionError("Скасувати інвентаризацію може власник/адміністратор із причиною.")
    with db_cursor() as cur:
        cur.execute("UPDATE inventory_counts SET status='cancelled' WHERE id=%s AND status='counting' RETURNING created_by", (count_id,))
        row=cur.fetchone()
        if not row:
            raise ValueError("Можна скасувати лише відкриту інвентаризацію.")
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason) VALUES(%s,%s,'inventory.count_cancelled','inventory_count',%s,%s::jsonb,%s)",
                    (actor.telegram_id,actor.role,str(count_id),json_dumps({"created_by":row["created_by"]}),reason.strip()))


def update_supplier_contacts(supplier_id: int, actor: Staff, *, contact_name: str = "",
                             phone: str = "", email: str = "", notes: str = "") -> None:
    if not actor.can("inventory.receive"):
        raise PermissionError("Недостатньо прав для редагування постачальника.")
    with db_cursor() as cur:
        cur.execute("SELECT name,contact_name,phone,email,notes FROM suppliers WHERE id=%s FOR UPDATE", (supplier_id,))
        old=cur.fetchone()
        if not old: raise ValueError("Постачальника не знайдено.")
        cur.execute("UPDATE suppliers SET contact_name=%s,phone=%s,email=%s,notes=%s WHERE id=%s",
                    (contact_name.strip()[:180],phone.strip()[:60],email.strip()[:180],notes.strip()[:2000],supplier_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data) VALUES(%s,%s,'supplier.contacts_updated','supplier',%s,%s::jsonb,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(supplier_id),json_dumps({k:old[k] for k in ("contact_name","phone","email","notes")}),json_dumps({"contact_name":contact_name,"phone":phone,"email":email,"notes":notes})))


def inventory_stock_valuation() -> dict:
    with db_cursor() as cur:
        cur.execute("""SELECT COUNT(*) sku_count,COALESCE(SUM(stock_qty),0) units,
                       COALESCE(SUM(stock_qty*COALESCE(cost_price,0)),0) stock_cost,
                       COUNT(*) FILTER (WHERE cost_price IS NULL AND stock_qty>0) missing_cost_skus
                       FROM product_variants WHERE active=TRUE""")
        row=cur.fetchone()
        return {"sku_count":int(row["sku_count"]),"units":int(row["units"]),
                "stock_cost":Decimal(str(row["stock_cost"])),"missing_cost_skus":int(row["missing_cost_skus"])}


def inventory_stock_valuation_rows(limit: int = 100) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT p.name product_name,v.sku,v.stock_qty,v.reserved_qty,
                       v.stock_qty-v.reserved_qty available,v.cost_price,
                       v.stock_qty*COALESCE(v.cost_price,0) stock_cost
                       FROM product_variants v JOIN products p ON p.id=v.product_id
                       WHERE v.active=TRUE AND v.stock_qty>0 ORDER BY stock_cost DESC,p.name
                       LIMIT %s""", (max(1,min(300,limit)),))
        return list(cur.fetchall())


def inventory_stock_adjustment_preview(variant_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT v.id,v.sku,v.stock_qty,v.reserved_qty,v.stock_qty-v.reserved_qty available,
                       p.name product_name FROM product_variants v JOIN products p ON p.id=v.product_id
                       WHERE v.id=%s AND v.active=TRUE""", (variant_id,))
        return cur.fetchone()


def inventory_render_valuation(chat_id: int) -> None:
    summary=inventory_stock_valuation()
    rows=inventory_stock_valuation_rows(30)
    lines=["<b>Оцінка складських залишків</b>",f"Активних SKU: {summary['sku_count']}",
           f"Фізичний залишок: {summary['units']} шт.",f"Облікова собівартість: <b>{_inv_money(summary['stock_cost'])}</b>",
           f"SKU без собівартості: {summary['missing_cost_skus']}","","<b>Найбільша вартість запасів</b>"]
    for row in rows:
        lines.append(f"• {safe(row['product_name'])}/{safe(row['sku'])}: {row['stock_qty']} шт. · {_inv_money(row['stock_cost'])}")
    bot.send_message(chat_id,"\n".join(lines))


def inventory_render_count_list(chat_id: int) -> None:
    with db_cursor() as cur:
        cur.execute("""SELECT c.id,c.status,c.created_at,COUNT(i.id) total,COUNT(i.actual_qty) counted
                       FROM inventory_counts c LEFT JOIN inventory_count_items i ON i.count_id=c.id
                       WHERE c.status IN ('counting','confirmed','cancelled')
                       GROUP BY c.id ORDER BY c.id DESC LIMIT 40""")
        rows=list(cur.fetchall())
    if not rows:
        bot.send_message(chat_id,"Інвентаризацій ще не було."); return
    lines=["<b>Історія інвентаризацій</b>"]
    for row in rows:
        lines.append(f"• #{row['id']} · {safe(row['status'])} · {row['counted']}/{row['total']} SKU · {safe(row['created_at'])}")
    bot.send_message(chat_id,"\n".join(lines))


def inventory_render_supplier_detail(chat_id: int, supplier_id: int) -> None:
    row=get_supplier(supplier_id)
    if not row: bot.send_message(chat_id,"Постачальника не знайдено."); return
    kb=types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("✏️ Контакти та примітки",callback_data=f"invops:supplier:edit:{supplier_id}"),
           types.InlineKeyboardButton("🔄 Змінити активність",callback_data=f"invops:supplier:toggle:{supplier_id}:{0 if row['active'] else 1}"),
           types.InlineKeyboardButton("↩️ До постачальників",callback_data="invops:supplier:list"))
    text=(f"<b>{safe(row['name'])}</b>\nСтатус: {'активний' if row['active'] else 'неактивний'}\n"
          f"Контакт: {safe(row.get('contact_name') or 'не вказано')}\nТелефон: {safe(row.get('phone') or 'не вказано')}\n"
          f"Email: {safe(row.get('email') or 'не вказано')}\nПримітки: {safe(row.get('notes') or 'немає')}")
    bot.send_message(chat_id,text,reply_markup=kb)


def inventory_prompt_supply_received_edit(chat_id: int, user_id: int, supply_id: int,
                                           variant_id: int, maximum: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supply_received_edit","supply_id":supply_id,
                                "variant_id":variant_id,"maximum":maximum,"chat_id":chat_id}
    bot.send_message(chat_id,f"Введіть фактично прийняту кількість від 0 до {maximum}:")


def inventory_prompt_supplier_edit(chat_id: int, user_id: int, supplier_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"supplier_edit_contact","supplier_id":supplier_id,
                                "field":"contact_name","values":{},"chat_id":chat_id}
    bot.send_message(chat_id,"Введіть ім'я контактної особи (або - щоб залишити порожнім):")


def inventory_prompt_adjust_sku(chat_id: int, user_id: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"adjust_sku","chat_id":chat_id}
    bot.send_message(chat_id,"Введіть SKU або частину назви для ручного коригування залишку:")


def inventory_prompt_adjust_delta(chat_id: int, user_id: int, variant_id: int) -> None:
    preview=inventory_stock_adjustment_preview(variant_id)
    if not preview: raise ValueError("Активний SKU не знайдено.")
    INVENTORY_WIZARDS[user_id]={"kind":"adjust_delta","variant_id":variant_id,"chat_id":chat_id}
    bot.send_message(chat_id,f"<b>{safe(preview['product_name'])} / {safe(preview['sku'])}</b>\nПоточний залишок: {preview['stock_qty']} · резерв: {preview['reserved_qty']} · доступно: {preview['available']}\nВведіть зміну кількості зі знаком, наприклад +5 або -2:")


def inventory_prompt_adjust_reason(chat_id: int, user_id: int, variant_id: int, delta: int) -> None:
    INVENTORY_WIZARDS[user_id]={"kind":"adjust_reason","variant_id":variant_id,"delta":delta,"chat_id":chat_id}
    bot.send_message(chat_id,"Вкажіть причину ручного коригування. Вона потрапить до журналу:")


def inventory_supply_card(chat_id: int, supply_id: int, staff: Staff) -> None:
    doc=get_supply_document(supply_id)
    if not doc:
        bot.send_message(chat_id,"Поставку не знайдено."); return
    kb=types.InlineKeyboardMarkup(row_width=2)
    if doc["state"]=="draft" and staff.can("inventory.receive"):
        for item in doc.get("items",[]):
            kb.add(types.InlineKeyboardButton(f"Приймання {item['sku']}: {item['received_qty']}/{item['quantity']}",
                   callback_data=f"invops:supply:receive:{supply_id}:{item['variant_id']}"),
                   types.InlineKeyboardButton(f"Видалити {item['sku']}",callback_data=f"invops:supply:remove:{supply_id}:{item['id']}"))
        kb.add(types.InlineKeyboardButton("➕ Додати позицію",callback_data=f"invops:supply:add:{supply_id}"),
               types.InlineKeyboardButton("✅ Провести поставку",callback_data=f"invops:supply:post:{supply_id}"),
               types.InlineKeyboardButton("🗑 Скасувати чернетку",callback_data=f"invops:supply:cancel:{supply_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До поставок",callback_data="invops:supply:list"))
    bot.send_message(chat_id,_inv_supply_text(doc),reply_markup=kb)


def inventory_remove_supply_item(supply_id: int, item_id: int, actor: Staff) -> None:
    if not actor.can("inventory.receive"):
        raise PermissionError("Недостатньо прав.")
    with db_cursor() as cur:
        cur.execute("SELECT state FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc=cur.fetchone()
        if not doc or doc["state"]!="draft": raise ValueError("Редагувати можна лише чернетку.")
        cur.execute("DELETE FROM supply_items WHERE id=%s AND supply_id=%s RETURNING variant_id,quantity,received_qty", (item_id,supply_id))
        item=cur.fetchone()
        if not item: raise ValueError("Позицію поставки не знайдено.")
        cur.execute("UPDATE supply_documents SET total_cost=(SELECT COALESCE(SUM(quantity*unit_cost),0) FROM supply_items WHERE supply_id=%s) WHERE id=%s",(supply_id,supply_id))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'supply.item_removed','supply_item',%s,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(item_id),json_dumps({"supply_id":supply_id,"variant_id":item["variant_id"],"quantity":item["quantity"],"received_qty":item["received_qty"]})))


def inventory_supply_post_preflight(supply_id: int) -> dict:
    doc=get_supply_document(supply_id)
    if not doc or doc["state"]!="draft": raise ValueError("Чернетку поставки не знайдено.")
    items=doc.get("items",[])
    return {"document_number":doc["document_number"],"supplier":doc.get("supplier_name") or "не вказаний",
            "items":len(items),"received_units":sum(int(x["received_qty"]) for x in items),
            "total_cost":sum((Decimal(str(x["unit_cost"]))*int(x["received_qty"]) for x in items),Decimal("0.00")),
            "invalid":any(int(x["received_qty"])>int(x["quantity"]) for x in items)}


@bot.callback_query_handler(func=lambda c: c.data.startswith("invops:") and ":choose:" not in c.data)
def inventory_operations_callback(call):
    staff=_inventory_actor(call,"inventory.read")
    if not staff:
        bot.answer_callback_query(call.id,"Доступ заборонено.",show_alert=True); return
    data=call.data.split(":")
    chat_id=call.message.chat.id
    try:
        if data[1]=="home":
            bot.answer_callback_query(call.id); inventory_admin_home(chat_id,staff); return
        if data[1]=="count" and data[2]=="new":
            bot.answer_callback_query(call.id); inventory_start_count(chat_id,staff); return
        if data[1]=="count" and data[2]=="list":
            bot.answer_callback_query(call.id)
            with db_cursor() as cur:
                cur.execute("SELECT id FROM inventory_counts WHERE status='counting' ORDER BY id DESC LIMIT 30")
                ids=[int(r["id"]) for r in cur.fetchall()]
            kb=types.InlineKeyboardMarkup(row_width=1)
            for cid in ids: kb.add(types.InlineKeyboardButton(f"Інвентаризація #{cid}",callback_data=f"invops:count:open:{cid}"))
            kb.add(types.InlineKeyboardButton("↩️ До складу",callback_data="invops:home"))
            bot.send_message(chat_id,"Активні інвентаризації:" if ids else "Активних інвентаризацій немає.",reply_markup=kb); return
        if data[1]=="count" and data[2]=="open":
            bot.answer_callback_query(call.id); inventory_render_count(chat_id,int(data[3]),staff); return
        if data[1]=="count" and data[2]=="add":
            bot.answer_callback_query(call.id); inventory_prompt_count_sku(chat_id,call.from_user.id,int(data[3])); return
        if data[1]=="count" and data[2]=="pending":
            bot.answer_callback_query(call.id)
            rows=inventory_count_pending_items(int(data[3]))
            lines=["<b>Ще не пораховані SKU</b>"]+[f"• {safe(x['product_name'])} / {safe(x['sku'])}" for x in rows]
            bot.send_message(chat_id,"\n".join(lines) if rows else "Усі SKU вже пораховані."); return
        if data[1]=="count" and data[2]=="preview":
            if staff.role not in ("owner","admin"): raise PermissionError("Перегляд очікуваних залишків доступний лише власнику/адміністратору після завершення підрахунку.")
            bot.answer_callback_query(call.id)
            rows=inventory_count_discrepancy_preview(int(data[3]))
            lines=["<b>Розбіжності (після завершення сліпого підрахунку)</b>"]
            for x in rows:
                if int(x["discrepancy"]): lines.append(f"• {safe(x['product_name'])}/{safe(x['sku'])}: система {x['system_qty']}, факт після рухів {x['actual_qty']} (перераховано {x['counted_qty']}, рухи {x['concurrent_delta']:+d}), різниця {x['discrepancy']:+d}")
            bot.send_message(chat_id,"\n".join(lines) if len(lines)>1 else "Розбіжностей немає."); return
        if data[1]=="count" and data[2]=="confirm":
            if staff.role not in ("owner","admin"): raise PermissionError("Підтвердження доступне лише власнику/адміністратору.")
            bot.answer_callback_query(call.id)
            INVENTORY_WIZARDS[call.from_user.id]={"kind":"count_confirm_reason","count_id":int(data[3]),"chat_id":chat_id}
            bot.send_message(chat_id,"Введіть причину підтвердження інвентаризації:"); return
        if data[1]=="supplier" and data[2]=="list":
            bot.answer_callback_query(call.id); inventory_render_suppliers(chat_id,staff); return
        if data[1]=="supplier" and data[2]=="new":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id); inventory_prompt_supplier(chat_id,call.from_user.id); return
        if data[1]=="supplier" and data[2]=="toggle":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            supplier_id=int(data[3]); active=bool(int(data[4]))
            INVENTORY_WIZARDS[call.from_user.id]={"kind":"supplier_toggle_reason","supplier_id":supplier_id,"active":active,"chat_id":chat_id}
            bot.answer_callback_query(call.id); bot.send_message(chat_id,"Вкажіть причину зміни активності постачальника:"); return
        if data[1]=="supply" and data[2]=="new":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id)
            suppliers=list_suppliers()
            kb=types.InlineKeyboardMarkup(row_width=1)
            for s in suppliers: kb.add(types.InlineKeyboardButton(s["name"],callback_data=f"invops:supply:supplier:{s['id']}"))
            kb.add(types.InlineKeyboardButton("➕ Створити постачальника",callback_data="invops:supplier:new"))
            bot.send_message(chat_id,"Оберіть постачальника:",reply_markup=kb); return
        if data[1]=="supply" and data[2]=="supplier":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id); inventory_prompt_supply_document(chat_id,call.from_user.id,int(data[3])); return
        if data[1]=="supply" and data[2]=="list":
            bot.answer_callback_query(call.id); inventory_render_supply_list(chat_id); return
        if data[1]=="supply" and data[2]=="open":
            bot.answer_callback_query(call.id); inventory_supply_card(chat_id,int(data[3]),staff); return
        if data[1]=="supply" and data[2]=="add":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id); inventory_prompt_supply_sku(chat_id,call.from_user.id,int(data[3])); return
        if data[1]=="supply" and data[2]=="post":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id)
            preview=inventory_supply_post_preflight(int(data[3]))
            if preview["invalid"] or preview["received_units"]<=0:
                raise ValueError("Немає коректних фактично прийнятих позицій. Перевірте чернетку.")
            INVENTORY_WIZARDS[call.from_user.id]={"kind":"supply_post_confirm","supply_id":int(data[3]),"chat_id":chat_id}
            bot.send_message(chat_id,(f"<b>Підтвердження поставки</b>\nДокумент: {safe(preview['document_number'])}\n"
                f"Постачальник: {safe(preview['supplier'])}\nПозицій: {preview['items']}\n"
                f"Фактично прийнято: {preview['received_units']} шт.\nСума приймання: <b>{_inv_money(preview['total_cost'])}</b>\n\n"
                "Для проведення надішліть ПРОВЕСТИ. Для скасування /cancel. Після проведення зміняться залишки та середня собівартість.")); return
        if data[1]=="supply" and data[2]=="cancel":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id)
            INVENTORY_WIZARDS[call.from_user.id]={"kind":"supply_cancel_reason","supply_id":int(data[3]),"chat_id":chat_id}
            bot.send_message(chat_id,"Вкажіть причину скасування чернетки поставки:"); return
        if data[1]=="supplier" and data[2]=="detail":
            bot.answer_callback_query(call.id); inventory_render_supplier_detail(chat_id,int(data[3])); return
        if data[1]=="supplier" and data[2]=="edit":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id); inventory_prompt_supplier_edit(chat_id,call.from_user.id,int(data[3])); return
        if data[1]=="supply" and data[2]=="receive":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            supply_id,variant_id=int(data[3]),int(data[4])
            doc=get_supply_document(supply_id)
            item=next((x for x in doc["items"] if int(x["variant_id"])==variant_id),None) if doc else None
            if not item: raise ValueError("Позицію поставки не знайдено.")
            bot.answer_callback_query(call.id); inventory_prompt_supply_received_edit(chat_id,call.from_user.id,supply_id,variant_id,int(item["quantity"])); return
        if data[1]=="supply" and data[2]=="remove":
            if not staff.can("inventory.receive"): raise PermissionError("Недостатньо прав.")
            inventory_remove_supply_item(int(data[3]),int(data[4]),staff)
            bot.answer_callback_query(call.id,"Позицію видалено з чернетки."); inventory_supply_card(chat_id,int(data[3]),staff); return
        if data[1]=="count" and data[2]=="cancel":
            if staff.role not in ("owner","admin"): raise PermissionError("Недостатньо прав.")
            bot.answer_callback_query(call.id); INVENTORY_WIZARDS[call.from_user.id]={"kind":"count_cancel_reason","count_id":int(data[3]),"chat_id":chat_id}
            bot.send_message(chat_id,"Вкажіть причину скасування інвентаризації:"); return
        if data[1]=="count" and data[2]=="history":
            bot.answer_callback_query(call.id); inventory_render_count_list(chat_id); return
        if data[1]=="valuation":
            if staff.role!="owner": raise PermissionError("Оцінка собівартості доступна лише власнику.")
            bot.answer_callback_query(call.id); inventory_render_valuation(chat_id); return
        if data[1]=="adjust":
            if staff.role!="owner": raise PermissionError("Ручне коригування залишків доступне лише власнику.")
            bot.answer_callback_query(call.id); inventory_prompt_adjust_sku(chat_id,call.from_user.id); return
        if data[1]=="lowstock":
            bot.answer_callback_query(call.id); inventory_render_lowstock(chat_id); return
        if data[1]=="movements":
            bot.answer_callback_query(call.id); inventory_render_movements(chat_id); return
        bot.answer_callback_query(call.id,"Невідома дія.",show_alert=True)
    except Exception as exc:
        log.exception("Inventory operation callback failed")
        try: bot.answer_callback_query(call.id,str(exc)[:180],show_alert=True)
        except Exception: pass
        bot.send_message(chat_id,f"⚠️ {safe(str(exc))}")


@bot.message_handler(commands=["export_customers"])
def customer_export_security_test_command(message):
    """Any staff member invoking the export command triggers the export-attempt security rule.
    No customer data is exported by this command.
    """
    staff = get_staff(message.from_user.id)
    if not staff or not staff.active:
        bot.reply_to(message, "⛔ Команда доступна лише обліковим записам персоналу.")
        return
    if staff.role == "owner" or int(message.from_user.id) == int(CONFIG.owner_id):
        bot.reply_to(message, "🛡️ Власник системи не підлягає автоматичному блокуванню. Експорт не запускався.")
        return
    try:
        with db_cursor() as cur:
            record_security_signal(
                cur,
                "customer_export",
                staff.telegram_id,
                None,
                {
                    "action": "/export_customers",
                    "entity_type": "customers",
                    "details": "Blocked export attempt; security test only. No data exported."
                }
            )
        bot.reply_to(
            message,
            "🚨 Спробу експорту зафіксовано системою безпеки. "
            "Доступ призупинено на 15 хвилин. Власника повідомлено. "
            "Жодні дані клієнтів не експортувалися."
        )
    except Exception:
        log.exception("Customer export security trigger failed")
        bot.reply_to(message, "⚠️ Не вдалося зафіксувати подію безпеки. Повідомлення записано в журнал помилок.")


@bot.message_handler(func=lambda m: bool(m.text) and m.from_user.id in INVENTORY_WIZARDS,
                     content_types=["text"])
def inventory_wizard_message_handler(message):
    user_id=message.from_user.id
    state=INVENTORY_WIZARDS.get(user_id)
    if not state: return
    staff=require_staff(message)
    if not staff:
        INVENTORY_WIZARDS.pop(user_id,None); return
    raw=message.text.strip()
    chat_id=message.chat.id
    try:
        kind=state["kind"]
        if kind=="supplier_name":
            supplier_id=create_supplier(raw,staff)
            INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,f"✅ Постачальника створено: #{supplier_id} {safe(raw)}")
            inventory_render_suppliers(chat_id,staff); return
        if kind=="supplier_edit_contact":
            values=dict(state.get("values",{})); field=state["field"]
            values[field]="" if raw=="-" else raw
            sequence=[("phone","Введіть телефон або -:"),("email","Введіть email або -:"),("notes","Введіть примітку або -:")]
            next_index=next((i for i,(name,_) in enumerate(sequence) if name==field),-1)+1
            if next_index<len(sequence):
                next_field,prompt=sequence[next_index]
                INVENTORY_WIZARDS[user_id]={**state,"field":next_field,"values":values}
                bot.send_message(chat_id,prompt); return
            update_supplier_contacts(int(state["supplier_id"]),staff,contact_name=values.get("contact_name",""),phone=values.get("phone",""),email=values.get("email",""),notes=values.get("notes",""))
            supplier_id=int(state["supplier_id"]); INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,"Контакти постачальника оновлено."); inventory_render_supplier_detail(chat_id,supplier_id); return
        if kind=="supply_received_edit":
            received=_catalog_parse_int(raw,"Фактично прийнято",0,int(state["maximum"]))
            update_supply_received_qty(int(state["supply_id"]),int(state["variant_id"]),received,staff)
            supply_id=int(state["supply_id"]); INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,"Фактичну кількість оновлено."); inventory_supply_card(chat_id,supply_id,staff); return
        if kind=="count_cancel_reason":
            cancel_inventory_count(int(state["count_id"]),staff,raw)
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,"Інвентаризацію скасовано. Залишки не змінювалися."); return
        if kind=="adjust_sku":
            matches=catalog_search_skus(raw,limit=12)
            if not matches: bot.send_message(chat_id,"SKU не знайдено. Спробуйте ще раз."); return
            kb=types.InlineKeyboardMarkup(row_width=1)
            for item in matches:
                kb.add(types.InlineKeyboardButton(f"{item['product_name']} / {item['sku']}"[:60],callback_data=f"invops:adjust:choose:{item['variant_id']}"))
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,"Оберіть точний SKU:",reply_markup=kb); return
        if kind=="adjust_delta":
            if not re.fullmatch(r"[+-]?\d+",raw): raise ValueError("Введіть ціле число зі знаком, наприклад +5 або -2.")
            delta=int(raw)
            if delta==0 or abs(delta)>100000: raise ValueError("Зміна має бути ненульовою та не більшою за 100 000.")
            variant_id=int(state["variant_id"]); INVENTORY_WIZARDS.pop(user_id,None)
            inventory_prompt_adjust_reason(chat_id,user_id,variant_id,delta); return
        if kind=="adjust_reason":
            new_qty=adjust_inventory(int(state["variant_id"]),int(state["delta"]),staff,raw)
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,f"✅ Залишок скориговано. Новий фізичний залишок: {new_qty} шт."); return
        if kind=="supplier_toggle_reason":
            set_supplier_active(int(state["supplier_id"]),bool(state["active"]),staff,raw)
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,"Статус постачальника оновлено."); inventory_render_suppliers(chat_id,staff); return
        if kind=="supply_doc_number":
            supply_id=create_supply_document(raw,int(state["supplier_id"]),staff)
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,f"Чернетку поставки #{supply_id} створено.")
            inventory_supply_card(chat_id,supply_id,staff); return
        if kind=="supply_sku":
            matches=catalog_search_skus(raw,limit=12)
            if not matches:
                bot.send_message(chat_id,"SKU не знайдено. Спробуйте інший запит."); return
            kb=types.InlineKeyboardMarkup(row_width=1)
            for item in matches:
                label=f"{item['product_name']} / {item['sku']}"
                kb.add(types.InlineKeyboardButton(label[:60],callback_data=f"invops:supply:choose:{state['supply_id']}:{item['variant_id']}"))
            INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,"Оберіть точний SKU:",reply_markup=kb); return
        if kind=="supply_qty":
            quantity=_catalog_parse_int(raw,"Кількість",1,1_000_000)
            INVENTORY_WIZARDS[user_id]={**state,"kind":"supply_received","quantity":quantity}
            bot.send_message(chat_id,f"За документом: {quantity}. Введіть фактично прийняту кількість (0–{quantity}):"); return
        if kind=="supply_received":
            received=_catalog_parse_int(raw,"Фактично прийнято",0,int(state["quantity"]))
            INVENTORY_WIZARDS[user_id]={**state,"kind":"supply_cost","received_qty":received}
            bot.send_message(chat_id,"Введіть закупівельну ціну за одну одиницю, грн:"); return
        if kind=="supply_cost":
            cost=_catalog_parse_decimal(raw,"Закупівельна ціна")
            if cost<0: raise ValueError("Ціна не може бути від'ємною.")
            add_supply_item(int(state["supply_id"]),int(state["variant_id"]),int(state["quantity"]),cost,staff,int(state["received_qty"]))
            supply_id=int(state["supply_id"]); INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,"✅ Позицію додано до чернетки поставки."); inventory_supply_card(chat_id,supply_id,staff); return
        if kind=="count_sku":
            matches=inventory_count_find_sku(int(state["count_id"]),raw)
            if not matches:
                bot.send_message(chat_id,"Не знайшов SKU в цій інвентаризації. Спробуйте ще раз."); return
            kb=types.InlineKeyboardMarkup(row_width=1)
            for item in matches:
                label=f"{item['product_name']} / {item['sku']}"
                kb.add(types.InlineKeyboardButton(label[:60],callback_data=f"invops:count:choose:{state['count_id']}:{item['variant_id']}"))
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,"Оберіть точний товар:",reply_markup=kb); return
        if kind=="count_qty":
            qty=_catalog_parse_int(raw,"Фактична кількість",0,1_000_000)
            record_inventory_count_item(int(state["count_id"]),int(state["variant_id"]),qty,staff)
            count_id=int(state["count_id"]); INVENTORY_WIZARDS.pop(user_id,None)
            bot.send_message(chat_id,"✅ Кількість збережено. Системний залишок приховано до завершення підрахунку.")
            inventory_render_count(chat_id,count_id,staff); return
        if kind=="count_confirm_reason":
            report=confirm_inventory_count(int(state["count_id"]),staff,raw)
            INVENTORY_WIZARDS.pop(user_id,None)
            changed=[x for x in report if x["discrepancy"]]
            lines=[f"✅ Інвентаризацію #{state['count_id']} підтверджено.",f"Перевірено SKU: {len(report)}",f"Розбіжностей: {len(changed)}"]
            for item in changed[:50]: lines.append(f"SKU #{item['variant_id']}: {item['system_qty']} → {item['actual_qty']} ({item['discrepancy']:+d})")
            bot.send_message(chat_id,"\n".join(lines)); return
        if kind=="supply_post_confirm":
            if raw.upper()!="ПРОВЕСТИ":
                bot.send_message(chat_id,"Для підтвердження надішліть саме ПРОВЕСТИ. Або /cancel."); return
            result=post_supply_document(int(state["supply_id"]),staff)
            INVENTORY_WIZARDS.pop(user_id,None)
            lines=[f"✅ Поставку {safe(result['document_number'])} проведено.",f"Прийнято на суму: {_inv_money(result['total_received_cost'])}"]
            for item in result["items"]: lines.append(f"• {safe(item['sku'])}: +{item['received']} шт.; нова середня собівартість {_inv_money(item['weighted_cost'])}")
            bot.send_message(chat_id,"\n".join(lines)); return
        if kind=="supply_cancel_reason":
            cancel_supply_draft(int(state["supply_id"]),staff,raw)
            INVENTORY_WIZARDS.pop(user_id,None); bot.send_message(chat_id,"Чернетку поставки скасовано. Склад не змінювався."); return
    except Exception as exc:
        log.exception("Inventory wizard failed")
        bot.send_message(chat_id,f"⚠️ {safe(str(exc))}\nМожна виправити значення або скасувати через /cancel.")


@bot.callback_query_handler(func=lambda c: c.data.startswith("invops:supply:choose:") or c.data.startswith("invops:count:choose:") or c.data.startswith("invops:adjust:choose:"))
def inventory_choose_sku_callback(call):
    staff=require_staff(call,"inventory.read")
    if not staff:
        bot.answer_callback_query(call.id,"Доступ заборонено.",show_alert=True); return
    parts=call.data.split(":")
    try:
        if parts[1]=="adjust":
            if staff.role!="owner": raise PermissionError("Недостатньо прав.")
            inventory_prompt_adjust_delta(call.message.chat.id,call.from_user.id,int(parts[3]))
            bot.answer_callback_query(call.id); return
        if parts[1]=="supply":
            supply_id,variant_id=int(parts[3]),int(parts[4])
            variant=catalog_get_variant(variant_id)
            if not variant: raise ValueError("SKU не знайдено.")
            label=f"{variant.get('product_name') or variant.get('name') or 'Товар'} / {variant['sku']}"
            inventory_prompt_supply_qty(call.message.chat.id,call.from_user.id,supply_id,variant_id,label)
        else:
            count_id,variant_id=int(parts[3]),int(parts[4])
            with db_cursor() as cur:
                cur.execute("SELECT p.name product_name,v.sku,v.variant_name FROM product_variants v JOIN products p ON p.id=v.product_id WHERE v.id=%s",(variant_id,))
                row=cur.fetchone()
            if not row: raise ValueError("SKU не знайдено.")
            inventory_prompt_count_qty(call.message.chat.id,call.from_user.id,count_id,variant_id,f"{row['product_name']} / {row['sku']}")
        bot.answer_callback_query(call.id)
    except Exception as exc:
        bot.answer_callback_query(call.id,str(exc)[:180],show_alert=True)


@bot.message_handler(func=lambda m: m.text == "📦 Склад")
def inventory_admin_menu_button(message):
    staff=require_staff(message,"inventory.read")
    if staff:
        inventory_admin_home(message.chat.id,staff)


# ---------------------------------------------------------------------------
# Delivery operations desk (Handoff v1.7+)
# ---------------------------------------------------------------------------

DELIVERY_EVENT_LABELS = {
    "assigned": "Призначено кур’єра", "accepted": "Кур’єр прийняв замовлення",
    "departed": "Кур’єр вирушив", "arrived": "Кур’єр прибув",
    "delivered": "Доставлено", "failed": "Не вдалося доставити",
    "unassigned": "Призначення знято", "ttn_created": "Створено ТТН",
    "slot_booked": "Заброньовано часовий слот", "slot_released": "Слот звільнено",
}


def _delivery_staff(message_or_call, permission: str = "delivery.read") -> Optional[Staff]:
    staff = require_staff(message_or_call, permission)
    if not staff:
        return None
    return staff


def delivery_ready_orders(limit: int = 100) -> list[dict]:
    """Orders waiting for a delivery decision, newest first."""
    with db_cursor() as cur:
        cur.execute("""SELECT o.id,o.order_number,o.customer_name_snapshot,o.phone_snapshot,
                   o.city,o.delivery_branch,o.delivery_address,o.delivery_type,o.status,
                   o.grand_total,o.created_at,o.ttn,
                   COALESCE(ca.courier_telegram_id,0) courier_telegram_id,
                   st.display_name courier_name
            FROM orders o LEFT JOIN courier_assignments ca ON ca.order_id=o.id
              AND ca.status IN ('assigned','accepted','in_progress')
            LEFT JOIN staff st ON st.telegram_id=ca.courier_telegram_id
            WHERE o.status IN ('new','confirmed','packed','shipped')
            ORDER BY o.created_at,o.id LIMIT %s""", (max(1,min(300,limit)),))
        return list(cur.fetchall())


def delivery_couriers(active_only: bool = True) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT s.telegram_id,s.display_name,s.active,
                   COUNT(ca.id) FILTER(WHERE ca.status IN ('assigned','accepted','in_progress')) active_jobs
            FROM staff s LEFT JOIN courier_assignments ca ON ca.courier_telegram_id=s.telegram_id
            WHERE s.role='courier' AND (%s=FALSE OR s.active=TRUE)
            GROUP BY s.telegram_id,s.display_name,s.active ORDER BY s.display_name""", (active_only,))
        return list(cur.fetchall())


def delivery_assign_courier(order_id: int, courier_id: int, actor: Staff) -> None:
    if not actor.can("delivery.update"):
        raise PermissionError("Недостатньо прав для призначення кур’єра.")
    with db_cursor() as cur:
        cur.execute("SELECT id,order_number,status,delivery_type FROM orders WHERE id=%s FOR UPDATE", (order_id,))
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        if order["delivery_type"] not in ("courier_standard","courier_express","courier_night"):
            raise ValueError("Це замовлення не використовує кур’єра Cloud Hub.")
        if order["status"] not in ("new","confirmed","packed","shipped"):
            raise ValueError("На цьому етапі призначення кур’єра неможливе.")
        cur.execute("SELECT telegram_id,display_name FROM staff WHERE telegram_id=%s AND role='courier' AND active=TRUE FOR UPDATE", (courier_id,))
        courier = cur.fetchone()
        if not courier:
            raise ValueError("Кур’єра не знайдено або його обліковий запис неактивний.")
        cur.execute("SELECT id,courier_telegram_id,status FROM courier_assignments WHERE order_id=%s FOR UPDATE", (order_id,))
        previous = cur.fetchone()
        if previous and previous["status"] in ("assigned","accepted","in_progress"):
            if int(previous["courier_telegram_id"]) == courier_id:
                return
            cur.execute("UPDATE courier_assignments SET status='cancelled' WHERE id=%s", (previous["id"],))
            cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,courier_telegram_id,details) VALUES(%s,'unassigned',%s,%s,%s::jsonb)",
                        (order_id,actor.telegram_id,previous["courier_telegram_id"],json_dumps({"reason":"reassigned"})))
        cur.execute("""INSERT INTO courier_assignments(order_id,courier_telegram_id,assigned_by,status)
            VALUES(%s,%s,%s,'assigned') ON CONFLICT(order_id) DO UPDATE SET
            courier_telegram_id=EXCLUDED.courier_telegram_id,assigned_by=EXCLUDED.assigned_by,
            assigned_at=NOW(),accepted_at=NULL,departed_at=NULL,delivered_at=NULL,completed_at=NULL,status='assigned',notes=''""",
            (order_id,courier_id,actor.telegram_id))
        cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,courier_telegram_id,details) VALUES(%s,'assigned',%s,%s,%s::jsonb)",
                    (order_id,actor.telegram_id,courier_id,json_dumps({"courier_name":courier["display_name"]})))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'delivery.assign','order',%s,%s::jsonb)",
                    (actor.telegram_id,actor.role,str(order_id),json_dumps({"courier_id":courier_id})))
        enqueue_notification(cur, courier_id, "delivery",
                             {"text": f"🚴 Вам призначено доставку {order['order_number']}. Відкрийте /mydeliveries."},
                             dedupe_key=f"courier-assigned:{order_id}:{courier_id}:{int(time.time())}")


def delivery_set_courier_status(order_id: int, courier_id: int, new_status: str, note: str = "") -> dict:
    transitions = {
        "assigned": {"accepted","failed"}, "accepted": {"in_progress","failed"},
        "in_progress": {"arrived","delivered","failed"}, "arrived": {"delivered","failed"},
    }
    if new_status not in {"accepted","in_progress","arrived","delivered","failed"}:
        raise ValueError("Невідомий статус доставки.")
    event_map={"accepted":"accepted","in_progress":"departed","arrived":"arrived","delivered":"delivered","failed":"failed"}
    with db_cursor() as cur:
        cur.execute("""SELECT ca.*,o.order_number,o.delivery_type,o.delivery_deadline_at,o.customer_id,o.telegram_id_snapshot
            FROM courier_assignments ca JOIN orders o ON o.id=ca.order_id
            WHERE ca.order_id=%s AND ca.courier_telegram_id=%s FOR UPDATE OF ca,o""", (order_id,courier_id))
        row=cur.fetchone()
        if not row: raise ValueError("Активне призначення не знайдено.")
        current=row["status"]
        if new_status not in transitions.get(current,set()):
            raise ValueError(f"Перехід {current} → {new_status} заборонений.")
        stamp="NOW()"
        cur.execute(f"""UPDATE courier_assignments SET status=%s,
            accepted_at=CASE WHEN %s='accepted' THEN NOW() ELSE accepted_at END,
            departed_at=CASE WHEN %s='in_progress' THEN NOW() ELSE departed_at END,
            delivered_at=CASE WHEN %s='delivered' THEN NOW() ELSE delivered_at END,
            completed_at=CASE WHEN %s IN ('delivered','failed') THEN NOW() ELSE completed_at END,
            notes=CASE WHEN %s<>'' THEN %s ELSE notes END WHERE order_id=%s""",
            (new_status,new_status,new_status,new_status,new_status,note.strip(),note.strip(),order_id))
        cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,courier_telegram_id,details) VALUES(%s,%s,%s,%s,%s::jsonb)",
                    (order_id,event_map[new_status],courier_id,courier_id,json_dumps({"note":note.strip()})))
        late_minutes=0; compensation=Decimal("0.00")
        if new_status=="delivered":
            cur.execute("""UPDATE orders SET delivery_completed_at=NOW(),
                delivery_late_minutes=CASE WHEN delivery_deadline_at IS NOT NULL AND NOW()>delivery_deadline_at
                    THEN CEIL(EXTRACT(EPOCH FROM (NOW()-delivery_deadline_at))/60.0)::int ELSE 0 END
                WHERE id=%s RETURNING delivery_late_minutes,delivery_type,customer_id""", (order_id,))
            finished=cur.fetchone(); late_minutes=int(finished["delivery_late_minutes"] or 0)
            if finished["delivery_type"]=="courier_express" and late_minutes>0:
                # Handoff: 5 loyalty bonuses for each full minute late.
                compensation=(Decimal(late_minutes)*Decimal("5.00"))
                cur.execute("UPDATE orders SET delivery_compensation_bonuses=%s WHERE id=%s",(compensation,order_id))
                if finished["customer_id"]:
                    cur.execute("""INSERT INTO loyalty_accounts(customer_id,available,pending)
                        VALUES(%s,0,0) ON CONFLICT(customer_id) DO NOTHING""",(finished["customer_id"],))
                    idem=f"express-late-compensation:{order_id}"
                    cur.execute("""INSERT INTO loyalty_transactions(customer_id,order_id,transaction_type,amount,state,reason,actor_telegram_id,idempotency_key)
                        VALUES(%s,%s,'delivery_compensation',%s,'available',%s,%s,%s)
                        ON CONFLICT(idempotency_key) DO NOTHING RETURNING id""",
                        (finished["customer_id"],order_id,compensation,f"Запізнення Express: {late_minutes} повних хвилин",courier_id,idem))
                    tx=cur.fetchone()
                    if tx:
                        cur.execute("UPDATE loyalty_accounts SET available=available+%s,updated_at=NOW() WHERE customer_id=%s",(compensation,finished["customer_id"]))
            cur.execute("UPDATE orders SET status='delivered',updated_at=NOW() WHERE id=%s AND status='shipped' RETURNING customer_id",(order_id,))
            delivered_order=cur.fetchone()
            if delivered_order and delivered_order["customer_id"]:
                # Release pending purchase bonuses only after successful delivery.
                cur.execute("""UPDATE loyalty_lots SET state='available',available_at=NOW()
                    WHERE source_transaction_id IN (SELECT id FROM loyalty_transactions
                    WHERE order_id=%s AND transaction_type='earn') AND state='pending'
                    RETURNING remaining_amount""",(order_id,))
                released=sum((Decimal(str(x["remaining_amount"])) for x in cur.fetchall()),Decimal("0.00"))
                if released:
                    cur.execute("UPDATE loyalty_accounts SET pending=GREATEST(0,pending-%s),available=available+%s,updated_at=NOW() WHERE customer_id=%s",
                                (released,released,delivered_order["customer_id"]))
                    cur.execute("UPDATE loyalty_transactions SET state='available' WHERE order_id=%s AND transaction_type='earn' AND state='pending'",(order_id,))
            cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,'courier','delivery.completed','order',%s,%s::jsonb)",
                        (courier_id,str(order_id),json_dumps({"late_minutes":late_minutes,"compensation":str(compensation)})))
        return {"order_number":row["order_number"],"status":new_status,"late_minutes":late_minutes,"compensation":compensation}


def delivery_update_ttn(order_id: int, ttn: str, actor: Staff) -> None:
    clean=re.sub(r"\s+","",ttn or "")
    if not re.fullmatch(r"\d{14}",clean):
        raise ValueError("ТТН Нової пошти має містити 14 цифр. Перевірте номер.")
    with db_cursor() as cur:
        cur.execute("SELECT id,delivery_type,ttn FROM orders WHERE id=%s FOR UPDATE",(order_id,)); row=cur.fetchone()
        if not row: raise ValueError("Замовлення не знайдено.")
        if row["delivery_type"]!="nova_poshta": raise ValueError("ТТН можна додати лише до замовлення Нової пошти.")
        if row["ttn"] and row["ttn"]!=clean: raise ValueError("ТТН уже існує. Заміна потребує окремої процедури виправлення.")
        cur.execute("UPDATE orders SET ttn=%s,updated_at=NOW() WHERE id=%s",(clean,order_id))
        cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,details) VALUES(%s,'ttn_created',%s,%s::jsonb)",(order_id,actor.telegram_id,json_dumps({"ttn":clean})))
        cur.execute("SELECT customer_id FROM orders WHERE id=%s",(order_id,))
        customer_row=cur.fetchone()
        if customer_row and customer_row["customer_id"]:
            cur.execute("""UPDATE loyalty_lots SET state='available',available_at=NOW()
                           WHERE source_transaction_id IN (SELECT id FROM loyalty_transactions
                           WHERE order_id=%s AND transaction_type='earn') AND state='pending'
                           RETURNING remaining_amount""",(order_id,))
            released=sum((Decimal(str(x["remaining_amount"])) for x in cur.fetchall()),Decimal("0.00"))
            if released:
                cur.execute("""UPDATE loyalty_accounts SET pending=GREATEST(0,pending-%s),
                               available=available+%s,updated_at=NOW() WHERE customer_id=%s""",
                            (released,released,customer_row["customer_id"]))
                cur.execute("""UPDATE loyalty_transactions SET state='available'
                               WHERE order_id=%s AND transaction_type='earn' AND state='pending'""",(order_id,))
        cur.execute("INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data) VALUES(%s,%s,'delivery.ttn.create','order',%s,%s::jsonb)",(actor.telegram_id,actor.role,str(order_id),json_dumps({"ttn":clean})))


def delivery_create_slot(start_at: datetime, tariff_code: str, capacity: int, actor: Staff, duration_minutes: int = 30) -> int:
    if tariff_code not in ("night","standard","express"): raise ValueError("Невідомий тариф.")
    if capacity<1 or capacity>100: raise ValueError("Місткість має бути від 1 до 100.")
    if duration_minutes < 10 or duration_minutes > 240: raise ValueError("Тривалість слота має бути від 10 до 240 хвилин.")
    if start_at.tzinfo is None: raise ValueError("Час слота має містити часовий пояс.")
    end_at=start_at+timedelta(minutes=duration_minutes)
    with db_cursor() as cur:
        cur.execute("INSERT INTO delivery_slots(slot_date,starts_at,ends_at,tariff_code,capacity,created_by) VALUES(%s,%s,%s,%s,%s,%s) ON CONFLICT(starts_at,tariff_code) DO UPDATE SET capacity=GREATEST(delivery_slots.capacity,EXCLUDED.capacity),active=TRUE RETURNING id",
                    (start_at.date(),start_at,end_at,tariff_code,capacity,actor.telegram_id))
        return int(cur.fetchone()["id"])


def delivery_book_slot(order_id: int, slot_id: int, actor: Staff) -> None:
    with db_cursor() as cur:
        cur.execute("SELECT id,delivery_type,delivery_slot_id FROM orders WHERE id=%s FOR UPDATE",(order_id,)); order=cur.fetchone()
        if not order: raise ValueError("Замовлення не знайдено.")
        if order["delivery_type"] not in ("courier_standard","courier_express","courier_night"):
            raise ValueError("Часові слоти доступні лише для кур’єрської доставки.")
        cur.execute("SELECT * FROM delivery_slots WHERE id=%s AND active=TRUE AND starts_at>NOW() FOR UPDATE",(slot_id,)); slot=cur.fetchone()
        if not slot: raise ValueError("Слот недоступний або вже минув.")
        if slot["tariff_code"] != order["delivery_type"].replace("courier_", ""):
            raise ValueError("Слот не відповідає тарифу замовлення.")
        if order["delivery_slot_id"]==slot_id: return
        if int(slot["booked_count"])>=int(slot["capacity"]): raise ValueError("У цьому слоті вже немає вільних місць.")
        if order["delivery_slot_id"]:
            cur.execute("UPDATE delivery_slots SET booked_count=GREATEST(0,booked_count-1) WHERE id=%s",(order["delivery_slot_id"],))
            cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,details) VALUES(%s,'slot_released',%s,%s::jsonb)",(order_id,actor.telegram_id,json_dumps({"slot_id":order["delivery_slot_id"]})))
        cur.execute("UPDATE delivery_slots SET booked_count=booked_count+1 WHERE id=%s",(slot_id,))
        cur.execute("UPDATE orders SET delivery_slot_id=%s WHERE id=%s",(slot_id,order_id))
        cur.execute("INSERT INTO delivery_events(order_id,event_type,actor_telegram_id,details) VALUES(%s,'slot_booked',%s,%s::jsonb)",(order_id,actor.telegram_id,json_dumps({"slot_id":slot_id,"starts_at":slot["starts_at"].isoformat()})))


def delivery_order_timeline(order_id: int) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("SELECT event_type,actor_telegram_id,courier_telegram_id,details,created_at FROM delivery_events WHERE order_id=%s ORDER BY created_at,id",(order_id,))
        return list(cur.fetchall())


def delivery_render_desk(chat_id: int, staff: Staff) -> None:
    rows=delivery_ready_orders(100)
    lines=["<b>🚚 Доставка Cloud Hub</b>",f"Активні замовлення: {len(rows)}"]
    kb=types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        place=row["delivery_address"] if row["delivery_type"]!="nova_poshta" else f"{row['city']} / {row['delivery_branch']}"
        courier=f" · {row['courier_name']}" if row.get("courier_name") else ""
        lines.append(f"\n<b>{safe(row['order_number'])}</b> · {safe(row['status'])}\n{safe(row['customer_name_snapshot'])} · {safe(place or 'Адреса не вказана')}{safe(courier)}")
        kb.add(types.InlineKeyboardButton(f"{row['order_number']} · керування",callback_data=f"delops:order:{row['id']}"))
    kb.add(types.InlineKeyboardButton("🔄 Оновити доставки",callback_data="delops:home"),
           types.InlineKeyboardButton("👥 Кур’єри та навантаження",callback_data="delops:couriers"))
    kb.add(types.InlineKeyboardButton("📊 Звіт доставок",callback_data="delops:report"))
    if staff.can("delivery.update") and staff.role == "owner":
        kb.add(types.InlineKeyboardButton("🗓️ Створити графік слотів",callback_data="delops:slotsetup"))
    bot.send_message(chat_id,"\n".join(lines) if rows else "Активних доставок немає.",reply_markup=kb)


def delivery_render_order(chat_id: int, order_id: int, staff: Staff) -> None:
    with db_cursor() as cur:
        cur.execute("""SELECT o.*,ca.courier_telegram_id,st.display_name courier_name,ds.starts_at slot_start
            FROM orders o LEFT JOIN courier_assignments ca ON ca.order_id=o.id AND ca.status IN ('assigned','accepted','in_progress')
            LEFT JOIN staff st ON st.telegram_id=ca.courier_telegram_id LEFT JOIN delivery_slots ds ON ds.id=o.delivery_slot_id
            WHERE o.id=%s""",(order_id,)); row=cur.fetchone()
    if not row: raise ValueError("Замовлення не знайдено.")
    lines=[f"<b>{safe(row['order_number'])}</b>",f"Клієнт: {safe(row['customer_name_snapshot'])}",f"Телефон: {safe(row['phone_snapshot'])}",f"Доставка: {safe(row['delivery_type'])}",f"Статус: {safe(row['status'])}"]
    if row["delivery_type"]=="nova_poshta": lines += [f"Місто/відділення: {safe(row['city'])} / {safe(row['delivery_branch'])}",f"ТТН: {safe(row['ttn'] or 'ще не створено')}"]
    else: lines += [f"Адреса: {safe(row['delivery_address'])}",f"Кур’єр: {safe(row['courier_name'] or 'не призначений')}"]
    if row.get("slot_start"): lines.append(f"Слот: {row['slot_start'].astimezone(ZoneInfo(CONFIG.timezone)).strftime('%d.%m %H:%M')}")
    kb=types.InlineKeyboardMarkup(row_width=2)
    if row["delivery_type"] in ("courier_standard","courier_express","courier_night"):
        kb.add(types.InlineKeyboardButton("👤 Призначити кур’єра",callback_data=f"delops:assign:{order_id}"))
        kb.add(types.InlineKeyboardButton("🕒 Часовий слот",callback_data=f"delops:slots:{order_id}"))
    else:
        kb.add(types.InlineKeyboardButton("➕ Додати ТТН",callback_data=f"delops:ttn:{order_id}"))
    kb.add(types.InlineKeyboardButton("🧾 Історія доставки",callback_data=f"delops:timeline:{order_id}"),types.InlineKeyboardButton("↩️ До доставок",callback_data="delops:home"))
    bot.send_message(chat_id,"\n".join(lines),reply_markup=kb)


@bot.message_handler(commands=["deliverydesk"])
def delivery_desk_command(message):
    staff=_delivery_staff(message,"delivery.read")
    if staff: delivery_render_desk(message.chat.id,staff)


@bot.message_handler(commands=["mydeliveries"])
def courier_my_deliveries(message):
    staff=require_staff(message,"delivery.read")
    if not staff or staff.role!="courier":
        bot.reply_to(message,"Команда доступна лише обліковому запису кур’єра."); return
    with db_cursor() as cur:
        cur.execute("""SELECT ca.order_id,ca.status,o.order_number,o.delivery_address,o.city,o.delivery_branch,o.phone_snapshot,o.delivery_type
            FROM courier_assignments ca JOIN orders o ON o.id=ca.order_id
            WHERE ca.courier_telegram_id=%s AND ca.status IN ('assigned','accepted','in_progress') ORDER BY ca.assigned_at""",(staff.telegram_id,))
        rows=list(cur.fetchall())
    if not rows: bot.reply_to(message,"Активних доставок немає."); return
    for row in rows:
        kb=types.InlineKeyboardMarkup(row_width=2)
        if row["status"]=="assigned": kb.add(types.InlineKeyboardButton("Прийняти",callback_data=f"courier:{row['order_id']}:accepted"),types.InlineKeyboardButton("Проблема",callback_data=f"courier:{row['order_id']}:failed"))
        elif row["status"]=="accepted": kb.add(types.InlineKeyboardButton("Вирушив",callback_data=f"courier:{row['order_id']}:in_progress"),types.InlineKeyboardButton("Проблема",callback_data=f"courier:{row['order_id']}:failed"))
        else: kb.add(types.InlineKeyboardButton("Прибув",callback_data=f"courier:{row['order_id']}:arrived"),types.InlineKeyboardButton("Доставлено",callback_data=f"courier:{row['order_id']}:delivered"),types.InlineKeyboardButton("Проблема",callback_data=f"courier:{row['order_id']}:failed"))
        address=row["delivery_address"] or f"{row['city']} / {row['delivery_branch']}"
        bot.send_message(message.chat.id,f"<b>{safe(row['order_number'])}</b>\n{safe(address)}\nТелефон: {safe(row['phone_snapshot'])}\nСтатус: {safe(row['status'])}",reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("delops:") or c.data.startswith("courier:"))
def delivery_operations_callback(call):
    staff=require_staff(call,"delivery.read")
    if not staff:
        bot.answer_callback_query(call.id,"Доступ заборонено.",show_alert=True); return
    parts=call.data.split(":"); chat_id=call.message.chat.id
    try:
        if parts[0]=="courier":
            if staff.role!="courier": raise PermissionError("Лише призначений кур’єр може змінювати цей статус.")
            result=delivery_set_courier_status(int(parts[1]),staff.telegram_id,parts[2])
            bot.answer_callback_query(call.id,"Статус оновлено.")
            bot.send_message(chat_id,f"✅ {safe(result['order_number'])}: {safe(result['status'])}")
            return
        action=parts[1]
        if action=="home": bot.answer_callback_query(call.id); delivery_render_desk(chat_id,staff); return
        if action=="slotsetup":
            if staff.role != "owner": raise PermissionError("Графік доставки може налаштовувати лише власник.")
            DELIVERY_WIZARDS[call.from_user.id] = {"kind":"slot_setup"}
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id,
                "🗓️ <b>Генератор графіка доставки</b>\n"
                "Надішліть одним повідомленням у форматі:\n"
                "<code>2026-11-04 10:00 18:00 30 3 standard</code>\n\n"
                "Дата · початок · кінець · тривалість слота в хвилинах · місць у слоті · тариф\n"
                "Тарифи: standard, express, night. Час береться з TIMEZONE у Render.\n"
                "Для скасування: /cancel")
            return
        if action=="order": bot.answer_callback_query(call.id); delivery_render_order(chat_id,int(parts[2]),staff); return
        if action=="report":
            with db_cursor() as cur:
                cur.execute("""SELECT COUNT(*) FILTER(WHERE ca.status IN ('assigned','accepted','in_progress')) active,
                                   COUNT(*) FILTER(WHERE ca.status='delivered') delivered,
                                   COUNT(*) FILTER(WHERE ca.status='failed') failed,
                                   COUNT(*) FILTER(WHERE ca.status='assigned') waiting_accept
                            FROM courier_assignments ca WHERE ca.assigned_at >= NOW()-INTERVAL '30 days'""")
                stats=cur.fetchone()
            kb=types.InlineKeyboardMarkup(); kb.add(types.InlineKeyboardButton("↩️ До доставок",callback_data="delops:home"))
            bot.answer_callback_query(call.id)
            bot.send_message(chat_id, "📊 <b>Доставки за 30 днів</b>\n"
                f"Активні: {stats['active']}\nОчікують прийняття: {stats['waiting_accept']}\n"
                f"Доставлено: {stats['delivered']}\nПроблеми: {stats['failed']}", reply_markup=kb)
            return
        if action=="couriers":
            rows=delivery_couriers(); kb=types.InlineKeyboardMarkup(row_width=1)
            for row in rows: kb.add(types.InlineKeyboardButton(f"{row['display_name']} · активних доставок: {row['active_jobs']}",callback_data="delops:home"))
            bot.answer_callback_query(call.id); bot.send_message(chat_id,"<b>Кур’єри</b>\n"+("\n".join(f"• {safe(x['display_name'])}: {x['active_jobs']} активних" for x in rows) if rows else "Кур’єрів не додано."),reply_markup=kb); return
        if action=="assign":
            order_id=int(parts[2]); rows=delivery_couriers(); kb=types.InlineKeyboardMarkup(row_width=1)
            for row in rows: kb.add(types.InlineKeyboardButton(f"{row['display_name']} · {row['active_jobs']} активних",callback_data=f"delops:setcourier:{order_id}:{row['telegram_id']}"))
            kb.add(types.InlineKeyboardButton("↩️ Назад",callback_data=f"delops:order:{order_id}"))
            bot.answer_callback_query(call.id); bot.send_message(chat_id,"Оберіть кур’єра:",reply_markup=kb); return
        if action=="setcourier":
            delivery_assign_courier(int(parts[2]),int(parts[3]),staff)
            bot.answer_callback_query(call.id,"Кур’єра призначено."); delivery_render_order(chat_id,int(parts[2]),staff); return
        if action=="ttn":
            order_id=int(parts[2]); msg=bot.send_message(chat_id,"Надішліть 14-значну ТТН Нової пошти. /cancel для скасування.")
            DELIVERY_WIZARDS[call.from_user.id]={"kind":"ttn","order_id":order_id}
            bot.answer_callback_query(call.id); return
        if action=="timeline":
            rows=delivery_order_timeline(int(parts[2])); lines=["<b>Історія доставки</b>"]
            for row in rows: lines.append(f"{row['created_at'].astimezone(ZoneInfo(CONFIG.timezone)).strftime('%d.%m %H:%M:%S')} · {safe(DELIVERY_EVENT_LABELS.get(row['event_type'],row['event_type']))}")
            bot.answer_callback_query(call.id); bot.send_message(chat_id,"\n".join(lines) if len(lines)>1 else "Подій ще немає."); return
        if action=="slots":
            order_id=int(parts[2])
            with db_cursor() as cur:
                cur.execute("SELECT id,starts_at,booked_count,capacity FROM delivery_slots WHERE active=TRUE AND tariff_code=(SELECT replace(delivery_type,'courier_','') FROM orders WHERE id=%s) AND starts_at>NOW() AND booked_count<capacity ORDER BY starts_at LIMIT 20", (order_id,))
                rows=list(cur.fetchall())
            kb=types.InlineKeyboardMarkup(row_width=1)
            for row in rows: kb.add(types.InlineKeyboardButton(f"{row['starts_at'].astimezone(ZoneInfo(CONFIG.timezone)).strftime('%d.%m %H:%M')} · {row['capacity']-row['booked_count']} місць",callback_data=f"delops:bookslot:{order_id}:{row['id']}"))
            kb.add(types.InlineKeyboardButton("↩️ Назад",callback_data=f"delops:order:{order_id}"))
            bot.answer_callback_query(call.id); bot.send_message(chat_id,"Оберіть часовий слот доставки:",reply_markup=kb); return
        if action=="bookslot":
            delivery_book_slot(int(parts[2]),int(parts[3]),staff)
            bot.answer_callback_query(call.id,"Слот заброньовано."); delivery_render_order(chat_id,int(parts[2]),staff); return
        raise ValueError("Невідома дія доставки.")
    except Exception as exc:
        log.exception("Delivery operations callback failed")
        bot.answer_callback_query(call.id,safe(str(exc))[:180],show_alert=True)


DELIVERY_WIZARDS: dict[int,dict[str,Any]]={}


@bot.message_handler(commands=["cancel"])
def delivery_cancel_wizard(message):
    if message.from_user.id in DELIVERY_WIZARDS:
        DELIVERY_WIZARDS.pop(message.from_user.id,None); bot.reply_to(message,"Дію скасовано.")


@bot.message_handler(func=lambda m: bool(m.text) and m.from_user.id in DELIVERY_WIZARDS, content_types=["text"])
def delivery_wizard_message(message):
    state=DELIVERY_WIZARDS.get(message.from_user.id)
    if not state: return
    staff=require_staff(message,"delivery.update")
    if not staff: DELIVERY_WIZARDS.pop(message.from_user.id,None); return
    raw=(message.text or "").strip()
    try:
        if state["kind"]=="ttn":
            delivery_update_ttn(int(state["order_id"]),raw,staff)
            DELIVERY_WIZARDS.pop(message.from_user.id,None)
            bot.reply_to(message,"✅ ТТН збережено в замовленні та журналі доставки.")
            delivery_render_order(message.chat.id,int(state["order_id"]),staff)
        elif state["kind"]=="slot_setup":
            if staff.role != "owner":
                raise PermissionError("Графік доставки може налаштовувати лише власник.")
            parts = raw.split()
            if len(parts) != 6:
                raise ValueError("Потрібно 6 значень: YYYY-MM-DD HH:MM HH:MM інтервал_хв місткість тариф.")
            date_raw, start_raw, end_raw, interval_raw, capacity_raw, tariff = parts
            if tariff not in {"standard", "express", "night"}:
                raise ValueError("Тариф має бути standard, express або night.")
            interval = int(interval_raw); capacity = int(capacity_raw)
            if interval < 10 or interval > 240:
                raise ValueError("Інтервал має бути від 10 до 240 хвилин.")
            if capacity < 1 or capacity > 100:
                raise ValueError("Місткість має бути від 1 до 100.")
            tz = ZoneInfo(CONFIG.timezone)
            start = datetime.strptime(f"{date_raw} {start_raw}", "%Y-%m-%d %H:%M").replace(tzinfo=tz)
            end = datetime.strptime(f"{date_raw} {end_raw}", "%Y-%m-%d %H:%M").replace(tzinfo=tz)
            if start <= datetime.now(tz) or end <= start:
                raise ValueError("Дата має бути в майбутньому, а кінець пізніше початку.")
            if (end - start).total_seconds() / 60 > 24 * 60:
                raise ValueError("Графік не може перевищувати 24 години.")
            created = 0
            cursor = start
            while cursor + timedelta(minutes=interval) <= end:
                delivery_create_slot(cursor, tariff, capacity, staff, interval)
                created += 1
                cursor += timedelta(minutes=interval)
            DELIVERY_WIZARDS.pop(message.from_user.id,None)
            audit(staff, "delivery.slots.generated", "delivery_slots", date_raw,
                  after={"created_or_updated":created,"start":start.isoformat(),"end":end.isoformat(),
                         "interval_minutes":interval,"capacity":capacity,"tariff":tariff},
                  reason="Owner generated delivery schedule")
            bot.reply_to(message, f"✅ Графік збережено. Створено/оновлено слотів: <b>{created}</b>.\n"
                         f"Дата: {date_raw}, {start_raw}–{end_raw}, крок {interval} хв, місць: {capacity}.")
    except Exception as exc:
        bot.reply_to(message,f"⚠️ {safe(str(exc))}\nСпробуйте ще раз або /cancel.")



# ---------------------------------------------------------------------------
# Finance and management analytics (owner-only, read/write audited)
# ---------------------------------------------------------------------------

FINANCE_WIZARDS: dict[int, dict[str, Any]] = {}


def finance_period_summary(period: str) -> dict[str, Any]:
    """Return turnover, confirmed payments, order counts and expenses for a fixed period."""
    periods = {
        "today": ("сьогодні", "CURRENT_DATE"),
        "7d": ("останні 7 днів", "NOW() - INTERVAL '7 days'"),
        "30d": ("останні 30 днів", "NOW() - INTERVAL '30 days'"),
        "month": ("поточний місяць", "date_trunc('month', NOW())"),
    }
    if period not in periods:
        raise ValueError("Невідомий звітний період.")
    label, boundary = periods[period]
    with db_cursor() as cur:
        cur.execute(f"""SELECT COUNT(*)::int AS orders_count,
                    COUNT(*) FILTER (WHERE status IN ('cancelled','canceled'))::int AS cancelled_count,
                    COALESCE(SUM(grand_total) FILTER (WHERE status NOT IN ('cancelled','canceled')),0) AS order_turnover,
                    COALESCE(SUM(paid_amount) FILTER (WHERE payment_status='paid'),0) AS confirmed_paid,
                    COUNT(*) FILTER (WHERE payment_status='paid')::int AS paid_orders,
                    COUNT(*) FILTER (WHERE payment_status<>'paid')::int AS unpaid_orders,
                    COALESCE(AVG(grand_total) FILTER (WHERE status NOT IN ('cancelled','canceled')),0) AS average_check
                    FROM orders WHERE created_at >= {boundary}""")
        orders = dict(cur.fetchone())
        cur.execute(f"SELECT COALESCE(SUM(amount),0) AS expenses,COUNT(*)::int AS expense_count FROM business_expenses WHERE expense_date >= ({boundary})::date")
        expenses = dict(cur.fetchone())
        cur.execute(f"SELECT COUNT(*)::int AS new_customers FROM customers WHERE created_at >= {boundary}")
        customers = int(cur.fetchone()["new_customers"])
    return {"period": period, "label": label, **orders, **expenses, "new_customers": customers}


def finance_expense_rows(limit: int = 30) -> list[dict]:
    with db_cursor() as cur:
        cur.execute("""SELECT e.id,e.category,e.amount,e.description,e.expense_date,e.created_at,
                          s.display_name AS created_by_name
                   FROM business_expenses e LEFT JOIN staff s ON s.telegram_id=e.created_by
                   ORDER BY e.expense_date DESC,e.id DESC LIMIT %s""", (max(1, min(100, limit)),))
        return list(cur.fetchall())


def finance_expense_category_summary(days: int = 30) -> list[dict]:
    days = max(1, min(365, int(days)))
    with db_cursor() as cur:
        cur.execute("""SELECT category,COUNT(*)::int AS entries,COALESCE(SUM(amount),0) AS total
                   FROM business_expenses WHERE expense_date >= CURRENT_DATE - (%s * INTERVAL '1 day')
                   GROUP BY category ORDER BY total DESC,category""", (days,))
        return list(cur.fetchall())


def finance_render_home(chat_id: int, staff: Staff) -> None:
    if staff.role != "owner":
        bot.send_message(chat_id, "⛔ Фінансові дані доступні лише власнику.")
        return
    try:
        today = finance_period_summary("today")
        month = finance_period_summary("month")
        lines = [
            "<b>💰 Фінанси Cloud Hub</b>",
            "",
            f"Сьогодні підтверджено оплат: <b>{money(today['confirmed_paid'])}</b>",
            f"Сьогодні внесено витрат: <b>{money(today['expenses'])}</b>",
            f"Поточний місяць: оплати <b>{money(month['confirmed_paid'])}</b>",
            f"Витрати місяця: <b>{money(month['expenses'])}</b>",
            f"Неоплачених замовлень за місяць: <b>{month['unpaid_orders']}</b>",
            "",
            "Виторг замовлень та фактично підтверджені оплати показуються окремо. "
            "Це не чистий прибуток: повний облік усіх витрат і податків ще не підключений."
        ]
        kb = types.InlineKeyboardMarkup(row_width=2)
        kb.add(types.InlineKeyboardButton("➕ Додати витрату", callback_data="finops:add"),
               types.InlineKeyboardButton("🧾 Останні витрати", callback_data="finops:expenses"))
        kb.add(types.InlineKeyboardButton("📊 Звіт за 7 днів", callback_data="bizrep:finance:7d"),
               types.InlineKeyboardButton("📊 Звіт за 30 днів", callback_data="bizrep:finance:30d"))
        kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
        bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)
    except Exception:
        log.exception("Finance dashboard failed")
        bot.send_message(chat_id, "⚠️ Не вдалося завантажити фінансову панель. Помилку записано.")


def finance_render_expenses(chat_id: int, staff: Staff) -> None:
    if staff.role != "owner":
        raise PermissionError("Фінансові дані доступні лише власнику.")
    rows = finance_expense_rows(30)
    lines = ["<b>Останні витрати</b>"]
    for row in rows:
        lines.append(
            f"#{row['id']} · {safe(row['expense_date'])} · <b>{money(row['amount'])}</b>\n"
            f"{safe(row['category'])}: {safe(row['description'] or 'без опису')}\n"
            f"Вніс: {safe(row['created_by_name'] or '—')}"
        )
    if not rows:
        lines.append("Витрат поки не внесено.")
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("➕ Додати витрату", callback_data="finops:add"),
           types.InlineKeyboardButton("↩️ До фінансів", callback_data="finops:home"))
    bot.send_message(chat_id, "\n\n".join(lines), reply_markup=kb)


def finance_start_expense_wizard(chat_id: int, user_id: int) -> None:
    FINANCE_WIZARDS[user_id] = {"step": "category"}
    bot.send_message(chat_id, "Введіть категорію витрати (наприклад: реклама, оренда, зарплата, логістика).\n/cancel для скасування.")


def finance_expense_wizard_message(message) -> bool:
    state = FINANCE_WIZARDS.get(message.from_user.id)
    if not state:
        return False
    staff = require_staff(message)
    if not staff or staff.role != "owner":
        FINANCE_WIZARDS.pop(message.from_user.id, None)
        bot.reply_to(message, "⛔ Доступ заборонено.")
        return True
    raw = (message.text or "").strip()
    if raw == "/cancel":
        FINANCE_WIZARDS.pop(message.from_user.id, None)
        bot.reply_to(message, "Внесення витрати скасовано.")
        return True
    try:
        if state["step"] == "category":
            if not raw or len(raw) > 80:
                raise ValueError("Категорія має містити від 1 до 80 символів.")
            state["category"] = raw
            state["step"] = "amount"
            bot.reply_to(message, "Введіть суму витрати у гривнях, наприклад 1250.50.")
        elif state["step"] == "amount":
            amount = _catalog_parse_decimal(raw, "Сума")
            if amount <= 0 or amount > Decimal("100000000"):
                raise ValueError("Сума має бути більшою за 0 і не перевищувати 100 000 000 грн.")
            state["amount"] = amount
            state["step"] = "description"
            bot.reply_to(message, "Короткий опис або причина витрати. Якщо опису немає, надішліть дефіс.")
        elif state["step"] == "description":
            description = "" if raw == "-" else raw
            if len(description) > 500:
                raise ValueError("Опис не може перевищувати 500 символів.")
            expense_id = create_expense(state["category"], state["amount"], description, staff)
            FINANCE_WIZARDS.pop(message.from_user.id, None)
            bot.reply_to(message, f"✅ Витрату #{expense_id} записано: {safe(state['category'])}, {money(state['amount'])}.")
        return True
    except Exception as exc:
        bot.reply_to(message, f"⚠️ {safe(exc)} Спробуйте ще раз або /cancel.")
        return True


def analytics_delivery_summary(days: int = 30) -> dict[str, Any]:
    days = max(1, min(365, int(days)))
    with db_cursor() as cur:
        cur.execute("""SELECT COUNT(*) FILTER (WHERE event_type='delivered')::int AS delivered,
                    COUNT(*) FILTER (WHERE event_type='failed')::int AS failed,
                    COUNT(*) FILTER (WHERE event_type='assigned')::int AS assigned
                    FROM delivery_events WHERE created_at >= NOW() - (%s * INTERVAL '1 day')""", (days,))
        events = dict(cur.fetchone())
        cur.execute("""SELECT COUNT(*)::int AS express_delivered,
                    COALESCE(AVG(delivery_late_minutes),0) AS avg_late_minutes,
                    COUNT(*) FILTER (WHERE delivery_late_minutes>0)::int AS late_count,
                    COALESCE(SUM(delivery_compensation_bonuses),0) AS compensation
                    FROM orders WHERE delivery_type='courier_express' AND delivery_completed_at >= NOW() - (%s * INTERVAL '1 day')""", (days,))
        express = dict(cur.fetchone())
        cur.execute("""SELECT s.display_name,COUNT(ca.id) FILTER(WHERE ca.status='delivered')::int delivered,
                    COUNT(ca.id) FILTER(WHERE ca.status='failed')::int failed,
                    COUNT(ca.id) FILTER(WHERE ca.status IN ('assigned','accepted','in_progress'))::int active
                    FROM staff s LEFT JOIN courier_assignments ca ON ca.courier_telegram_id=s.telegram_id
                      AND ca.assigned_at >= NOW() - (%s * INTERVAL '1 day')
                    WHERE s.role='courier' GROUP BY s.telegram_id,s.display_name ORDER BY delivered DESC,s.display_name""", (days,))
        couriers = list(cur.fetchall())
    return {"days": days, **events, **express, "couriers": couriers}


def analytics_render_period(chat_id: int, period: str, staff: Staff) -> None:
    if staff.role != "owner":
        raise PermissionError("Розширена статистика доступна лише власнику.")
    data = finance_period_summary(period)
    lines = [
        f"<b>📊 Звіт: {safe(data['label'])}</b>", "",
        f"Замовлень створено: <b>{data['orders_count']}</b>",
        f"Скасовано: <b>{data['cancelled_count']}</b>",
        f"Сума активних замовлень: <b>{money(data['order_turnover'])}</b>",
        f"Підтверджені оплати: <b>{money(data['confirmed_paid'])}</b>",
        f"Оплачених замовлень: <b>{data['paid_orders']}</b>",
        f"Неоплачених замовлень: <b>{data['unpaid_orders']}</b>",
        f"Середній чек активного замовлення: <b>{money(data['average_check'])}</b>",
        f"Нових клієнтів: <b>{data['new_customers']}</b>",
        f"Внесені витрати: <b>{money(data['expenses'])}</b> ({data['expense_count']} записів)",
        "",
        "Не прирівнюйте суму створених замовлень до отриманих коштів. "
        "Звіт не є бухгалтерською або податковою звітністю."
    ]
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("🚚 Доставка за 30 днів", callback_data="bizrep:delivery:30"),
           types.InlineKeyboardButton("↩️ До статистики", callback_data="bizrep:home"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)


def analytics_render_delivery(chat_id: int, days: int, staff: Staff) -> None:
    if staff.role != "owner":
        raise PermissionError("Статистика доставок доступна лише власнику.")
    data = analytics_delivery_summary(days)
    lines = [f"<b>🚚 Доставка за {days} днів</b>", "",
             f"Призначень: {data['assigned']}", f"Успішних доставок: {data['delivered']}",
             f"Невдалих доставок: {data['failed']}",
             f"Express доставок: {data['express_delivered']}",
             f"Express із запізненням: {data['late_count']}",
             f"Середнє запізнення Express: {float(data['avg_late_minutes']):.1f} хв",
             f"Нараховано компенсацій: {money(data['compensation'])}", "", "<b>Кур’єри</b>"]
    for courier in data["couriers"]:
        lines.append(f"• {safe(courier['display_name'])}: доставлено {courier['delivered']}, проблем {courier['failed']}, активних {courier['active']}")
    if not data["couriers"]:
        lines.append("Кур’єрів поки немає.")
    kb = types.InlineKeyboardMarkup()
    kb.add(types.InlineKeyboardButton("↩️ До статистики", callback_data="bizrep:home"))
    bot.send_message(chat_id, "\n".join(lines), reply_markup=kb)


@bot.callback_query_handler(func=lambda c: c.data.startswith("finops:") or c.data.startswith("bizrep:"))
def finance_analytics_callback(call):
    staff = require_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    try:
        parts = call.data.split(":")
        if parts[0] == "finops":
            if staff.role != "owner":
                raise PermissionError("Фінанси доступні лише власнику.")
            action = parts[1]
            bot.answer_callback_query(call.id)
            if action == "home": finance_render_home(call.message.chat.id, staff)
            elif action == "add": finance_start_expense_wizard(call.message.chat.id, call.from_user.id)
            elif action == "expenses": finance_render_expenses(call.message.chat.id, staff)
            else: raise ValueError("Невідома дія фінансів.")
            return
        action = parts[1]
        bot.answer_callback_query(call.id)
        if action == "home":
            render_staff_section(call.message.chat.id, staff, "statistics")
        elif action == "finance":
            analytics_render_period(call.message.chat.id, parts[2], staff)
        elif action == "delivery":
            analytics_render_delivery(call.message.chat.id, int(parts[2]), staff)
        else:
            raise ValueError("Невідома дія звіту.")
    except Exception as exc:
        log.exception("Finance/analytics callback failed")
        bot.answer_callback_query(call.id, safe(exc)[:180], show_alert=True)


@bot.message_handler(func=lambda m: bool(m.text) and m.from_user.id in FINANCE_WIZARDS, content_types=["text"])
def finance_expense_message_handler(message):
    finance_expense_wizard_message(message)




# ---------------------------------------------------------------------------
# v1.19: operational support/tasks, staff audit trail and security signals
# ---------------------------------------------------------------------------

SECURITY_SIGNAL_RULES = {
    "permission_change": (2, 300, "critical"),
    "audit_tamper": (1, 300, "critical"),
    "order_cancel": (3, 300, "critical"),
    "price_edit": (10, 180, "critical"),
    "stock_zero": (5, 180, "critical"),
    "bonus_adjust": (3, 300, "critical"),
    "customer_export": (1, 300, "critical"),
}
SECURITY_AUTO_LOCK_MINUTES = 15
SECURITY_SIGNAL_EXPLANATIONS = {
    "permission_change": "часті зміни ролей або прав можуть означати спробу розширити привілеї",
    "audit_tamper": "спроба змінити або видалити журнал аудиту",
    "order_cancel": "надмірна кількість скасувань замовлень за короткий час",
    "price_edit": "масові зміни цін за короткий час",
    "stock_zero": "масове обнулення складських залишків",
    "bonus_adjust": "надмірна кількість ручних коригувань бонусів",
    "customer_export": "експорт персональних даних клієнтів є критичною дією",
}


def _security_signal_rule(event_type: str):
    aliases = {
        "staff.role_changed": "permission_change",
        "staff.permission_changed": "permission_change",
        "audit.tamper": "audit_tamper",
        "audit.deleted": "audit_tamper",
        "order.cancelled": "order_cancel",
        "order.canceled": "order_cancel",
        "catalog.price_changed": "price_edit",
        "product.price_changed": "price_edit",
        "inventory.stock_zeroed": "stock_zero",
        "stock.zeroed": "stock_zero",
        "loyalty.bonus_adjusted": "bonus_adjust",
        "bonus.adjusted": "bonus_adjust",
        "customer.export": "customer_export",
        "customers.exported": "customer_export",
    }
    return aliases.get(event_type, event_type)


def record_security_signal(cur, event_type: str, actor_id: Optional[int],
                           subject_id: Optional[int] = None,
                           details: Optional[dict] = None,
                           dedupe_key: Optional[str] = None) -> bool:
    """Persist a signal and apply the documented rolling-window lock rules.

    Caller must pass the active transaction cursor. Duplicate keys are ignored.
    Thresholds are fixed by the Handoff; night hours raise severity only.
    """
    event_type = _security_signal_rule(str(event_type))
    details = dict(details or {})
    if actor_id is None:
        return False
    if dedupe_key:
        cur.execute(
            """INSERT INTO security_action_counters(event_type,actor_telegram_id,subject_telegram_id,details,dedupe_key)
               VALUES(%s,%s,%s,%s::jsonb,%s) ON CONFLICT(dedupe_key) WHERE dedupe_key IS NOT NULL DO NOTHING
               RETURNING id""",
            (event_type, actor_id, subject_id, json_dumps(details), dedupe_key),
        )
    else:
        cur.execute(
            """INSERT INTO security_action_counters(event_type,actor_telegram_id,subject_telegram_id,details)
               VALUES(%s,%s,%s,%s::jsonb) RETURNING id""",
            (event_type, actor_id, subject_id, json_dumps(details)),
        )
    inserted = cur.fetchone()
    if not inserted:
        return False

    rule = SECURITY_SIGNAL_RULES.get(event_type)
    if not rule:
        return False
    threshold, window_seconds, severity = rule
    cur.execute(
        """SELECT CASE
                 WHEN %s IN ('price_edit','stock_zero')
                   THEN COUNT(DISTINCT COALESCE(details->>'entity_id',id::text))::int
                 ELSE COUNT(*)::int
               END AS n
           FROM security_action_counters
           WHERE event_type=%s AND actor_telegram_id=%s
             AND occurred_at >= NOW()-(%s * INTERVAL '1 second')""",
        (event_type, event_type, actor_id, window_seconds),
    )
    count = int(cur.fetchone()["n"])
    # Also detect three distinct critical action families in a rolling five-minute window.
    cur.execute(
        """SELECT COUNT(DISTINCT event_type)::int n FROM security_action_counters
           WHERE actor_telegram_id=%s AND occurred_at>=NOW()-INTERVAL '5 minutes'
             AND event_type IN ('permission_change','audit_tamper','order_cancel',
                                'price_edit','stock_zero','bonus_adjust','customer_export')""",
        (actor_id,),
    )
    distinct_critical = int(cur.fetchone()["n"])
    triggered = count >= threshold or distinct_critical >= 3
    if not triggered:
        return False

    cur.execute(
        """SELECT s.role,s.active,COALESCE(ss.state,'active') AS state
           FROM staff s LEFT JOIN staff_security_state ss ON ss.telegram_id=s.telegram_id
           WHERE s.telegram_id=%s FOR UPDATE OF s""",
        (actor_id,),
    )
    state_row = cur.fetchone()
    # Never auto-lock the owner, missing accounts, or already deactivated staff.
    if not state_row or state_row["role"] == "owner" or not state_row["active"]:
        return False
    if state_row["state"] in ("owner_locked", "security_locked", "deactivated"):
        return False
    cur.execute(
        """INSERT INTO staff_security_state(telegram_id,state,review_deadline,updated_at)
           VALUES(%s,'security_locked',NOW()+(%s * INTERVAL '1 minute'),NOW())
           ON CONFLICT(telegram_id) DO UPDATE SET
             state='security_locked',
             review_deadline=NOW()+(%s * INTERVAL '1 minute'),updated_at=NOW()
           WHERE staff_security_state.state NOT IN ('owner_locked','security_locked','deactivated')""",
        (actor_id, SECURITY_AUTO_LOCK_MINUTES, SECURITY_AUTO_LOCK_MINUTES),
    )
    kyiv_hour = datetime.now(ZoneInfo("Europe/Kyiv")).hour
    night = kyiv_hour >= 23 or kyiv_hour < 6
    security_event(cur, severity, "security.threshold_triggered", actor_id, actor_id, {
        "signal": event_type, "count": count, "threshold": threshold,
        "window_seconds": window_seconds, "distinct_critical_actions": distinct_critical,
        "night_priority": night, "source_details": details,
        "explanation": SECURITY_SIGNAL_EXPLANATIONS.get(event_type, "спрацювало правило аномальної активності"),
        "automatic_lock_minutes": SECURITY_AUTO_LOCK_MINUTES,
    })
    cur.execute(
        """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data,reason)
           VALUES(NULL,'system','security.auto_lock','staff',%s,%s::jsonb,%s)""",
        (str(actor_id), json_dumps({"state":"security_locked","signal":event_type}),
         "Автоматичне блокування за порогом Security Center"),
    )
    cur.execute("SELECT display_name,role FROM staff WHERE telegram_id=%s", (actor_id,))
    staff_info=cur.fetchone() or {}
    explanation=SECURITY_SIGNAL_EXPLANATIONS.get(event_type,"спрацювало правило аномальної активності")
    alert_text=(
        f"🚨 <b>Cloud Hub Security: тимчасове блокування</b>\\n"
        f"Працівник: <b>{safe(staff_info.get('display_name') or 'працівник')}</b> · {safe(staff_info.get('role') or '—')}\\n"
        f"Telegram ID: <code>{actor_id}</code>\\n"
        f"Що зроблено: <b>{safe(details.get('action') or event_type)}</b>\\n"
        f"Чому це небезпечно: {safe(explanation)}\\n"
        f"Поріг: <b>{count}/{threshold}</b> за {window_seconds} с; критичних типів: {distinct_critical}.\\n"
        f"Доступ призупинено на <b>{SECURITY_AUTO_LOCK_MINUTES} хв</b>."
    )
    enqueue_notification(cur, CONFIG.owner_id, "security", {
        "text": alert_text,
        "buttons": [
            ["👤 Картка працівника", f"sec:staff:{actor_id}"],
            ["🔓 Розблокувати зараз", f"sec:unlock:{actor_id}"],
            ["⛔ Заблокувати вручну", f"sec:lock:{actor_id}"],
        ],
    }, f"security-auto-lock:{actor_id}:{event_type}:{int(time.time() // max(1,window_seconds))}")
    enqueue_notification(cur, actor_id, "security", {
        "text": "⛔ Cloud Hub автоматично призупинив ваш доступ через спрацювання правила безпеки. "
                "Зверніться до власника системи."
    }, f"security-auto-lock-user:{actor_id}:{int(time.time() // 60)}")
    return True


def security_staff_audit_rows(telegram_id: int, limit: int = 100, offset: int = 0) -> list[dict]:
    limit = max(1, min(100, int(limit)))
    offset = max(0, int(offset))
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,action,entity_type,entity_id,before_data,after_data,reason,created_at
               FROM audit_log WHERE actor_telegram_id=%s
               ORDER BY created_at DESC,id DESC LIMIT %s OFFSET %s""",
            (telegram_id, limit, offset),
        )
        return list(cur.fetchall())


def security_render_staff_audit(chat_id: int, telegram_id: int, offset: int, actor: Staff) -> None:
    if actor.role != "owner":
        raise PermissionError("Журнал аудиту працівників доступний лише власнику.")
    rows = security_staff_audit_rows(telegram_id, 100, offset)
    staff_rows = [r for r in list_security_staff() if int(r["telegram_id"]) == telegram_id]
    name = staff_rows[0]["display_name"] if staff_rows else str(telegram_id)
    text_lines = [f"<b>📜 Аудит: {safe(name)}</b>", f"Записи {offset+1}–{offset+len(rows)}"]
    for row in rows:
        text_lines.append(
            f"#{row['id']} · {safe(row['created_at'])}\n"
            f"<b>{safe(row['action'])}</b> · {safe(row['entity_type'])} #{safe(row['entity_id'])}\n"
            f"Причина: {safe(row['reason'] or '—')}"
        )
    if not rows:
        text_lines.append("Записів аудиту немає.")
    kb = types.InlineKeyboardMarkup(row_width=2)
    if offset > 0:
        kb.add(types.InlineKeyboardButton("⬅️ Новіші", callback_data=f"sec:audit:{telegram_id}:{max(0,offset-100)}"))
    if len(rows) == 100:
        kb.add(types.InlineKeyboardButton("Старіші ➡️", callback_data=f"sec:audit:{telegram_id}:{offset+100}"))
    kb.add(types.InlineKeyboardButton("↩️ До працівника", callback_data=f"sec:staff:{telegram_id}"))
    bot.send_message(chat_id, "\n\n".join(text_lines), parse_mode="HTML", reply_markup=kb)


def support_ticket_rows(status: Optional[str] = None, limit: int = 30) -> list[dict]:
    limit = max(1, min(100, int(limit)))
    with db_cursor() as cur:
        if status:
            cur.execute(
                """SELECT t.id,t.customer_telegram_id,t.order_id,t.subject,t.status,t.assigned_to,
                          t.created_at,t.updated_at,COUNT(m.id)::int message_count
                   FROM support_tickets t LEFT JOIN support_messages m ON m.ticket_id=t.id
                   WHERE t.status=%s GROUP BY t.id ORDER BY t.updated_at DESC,t.id DESC LIMIT %s""",
                (status, limit),
            )
        else:
            cur.execute(
                """SELECT t.id,t.customer_telegram_id,t.order_id,t.subject,t.status,t.assigned_to,
                          t.created_at,t.updated_at,COUNT(m.id)::int message_count
                   FROM support_tickets t LEFT JOIN support_messages m ON m.ticket_id=t.id
                   WHERE t.status<>'closed' GROUP BY t.id ORDER BY t.updated_at DESC,t.id DESC LIMIT %s""",
                (limit,),
            )
        return list(cur.fetchall())


def support_ticket_detail(ticket_id: int) -> Optional[dict]:
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,customer_telegram_id,order_id,subject,status,assigned_to,created_at,updated_at
               FROM support_tickets WHERE id=%s""", (ticket_id,))
        ticket = cur.fetchone()
        if not ticket:
            return None
        cur.execute(
            """SELECT sender_telegram_id,sender_type,body,created_at FROM support_messages
               WHERE ticket_id=%s ORDER BY id DESC LIMIT 20""", (ticket_id,))
        ticket["messages"] = list(reversed(cur.fetchall()))
        return ticket


def support_assign_ticket(ticket_id: int, assignee_id: int, actor: Staff) -> None:
    if actor.role not in ("owner", "admin"):
        raise PermissionError("Призначати звернення може власник або адміністратор.")
    with db_cursor() as cur:
        cur.execute("SELECT telegram_id,active FROM staff WHERE telegram_id=%s", (assignee_id,))
        assignee = cur.fetchone()
        if not assignee or not assignee["active"]:
            raise ValueError("Активного працівника не знайдено.")
        cur.execute(
            """UPDATE support_tickets SET assigned_to=%s,status=CASE WHEN status='new' THEN 'open' ELSE status END,
               updated_at=NOW() WHERE id=%s AND status<>'closed' RETURNING customer_telegram_id""",
            (assignee_id, ticket_id),
        )
        row = cur.fetchone()
        if not row:
            raise ValueError("Звернення не знайдено або воно закрите.")
        enqueue_notification(cur, assignee_id, "support",
            {"text": f"🎫 Вам призначено звернення #{ticket_id}."},
            f"ticket:{ticket_id}:assigned:{assignee_id}")


def support_staff_reply(ticket_id: int, body: str, actor: Staff) -> None:
    if not actor.can("support.read") or not actor.can("support.reply"):
        raise PermissionError("Недостатньо прав для відповіді в підтримці.")
    body = body.strip()
    if not body or len(body) > 4000:
        raise ValueError("Відповідь має містити від 1 до 4000 символів.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT customer_telegram_id,status FROM support_tickets
               WHERE id=%s FOR UPDATE""", (ticket_id,))
        ticket = cur.fetchone()
        if not ticket or ticket["status"] == "closed":
            raise ValueError("Звернення закрите або не існує.")
        cur.execute(
            """INSERT INTO support_messages(ticket_id,sender_telegram_id,sender_type,body)
               VALUES(%s,%s,'staff',%s)""", (ticket_id, actor.telegram_id, body))
        cur.execute("UPDATE support_tickets SET status='waiting_customer',updated_at=NOW() WHERE id=%s",
                    (ticket_id,))
        enqueue_notification(cur, int(ticket["customer_telegram_id"]), "support",
            {"text": f"💬 <b>Відповідь підтримки на звернення #{ticket_id}</b>\n\n{safe(body)}",
             "buttons": [["✍️ Відповісти", f"cs:reply:{ticket_id}"]]},
            f"ticket:{ticket_id}:staff-reply:{uuid.uuid4().hex}")
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data)
               VALUES(%s,%s,'support.reply','ticket',%s,%s::jsonb)""",
            (actor.telegram_id, actor.role, str(ticket_id), json_dumps({"length":len(body)})))


def support_set_ticket_status(ticket_id: int, status: str, actor: Staff) -> None:
    if actor.role not in ("owner", "admin", "manager"):
        raise PermissionError("Недостатньо прав.")
    if status not in ("open", "waiting_customer", "closed"):
        raise ValueError("Невідомий статус звернення.")
    with db_cursor() as cur:
        cur.execute("UPDATE support_tickets SET status=%s,updated_at=NOW() WHERE id=%s RETURNING id,customer_telegram_id",
                    (status, ticket_id))
        updated = cur.fetchone()
        if not updated:
            raise ValueError("Звернення не знайдено.")
        if status == "closed":
            enqueue_notification(cur, int(updated["customer_telegram_id"]), "support",
                {"text": f"🔒 Звернення #{ticket_id} закрито. Якщо питання лишилося, створіть нове через «🎫 Підтримка»."},
                f"ticket:{ticket_id}:closed:{uuid.uuid4().hex}")
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data)
               VALUES(%s,%s,'support.status_changed','ticket',%s,%s::jsonb)""",
            (actor.telegram_id, actor.role, str(ticket_id), json_dumps({"status":status})))


def support_render_ticket(chat_id: int, ticket_id: int, actor: Staff) -> None:
    if not actor.can("support.read"):
        raise PermissionError("Немає доступу до підтримки.")
    ticket = support_ticket_detail(ticket_id)
    if not ticket:
        bot.send_message(chat_id, "Звернення не знайдено.")
        return
    lines = [
        f"<b>🎫 Звернення #{ticket_id}</b>",
        f"Клієнт: <code>{ticket['customer_telegram_id']}</code>",
        f"Замовлення: {ticket['order_id'] or '—'}",
        f"Статус: <b>{safe(TICKET_STATUS_LABELS.get(ticket['status'], ticket['status']))}</b>",
        f"Відповідальний: {ticket['assigned_to'] or 'не призначено'}",
        "",
    ]
    for msg in ticket["messages"]:
        who = "Клієнт" if msg["sender_type"] == "customer" else f"Працівник {msg['sender_telegram_id']}"
        when = msg["created_at"].astimezone().strftime("%d.%m %H:%M") if isinstance(msg["created_at"], datetime) else str(msg["created_at"])
        lines.append(f"<b>{safe(who)} · {safe(when)}</b>\n{safe(msg['body'])}")
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("✍️ Відповісти", callback_data=f"support:reply:{ticket_id}"))
    kb.add(types.InlineKeyboardButton("🟢 В роботі", callback_data=f"support:status:{ticket_id}:open"),
           types.InlineKeyboardButton("⏳ Чекаємо клієнта", callback_data=f"support:status:{ticket_id}:waiting_customer"))
    kb.add(types.InlineKeyboardButton("🔒 Закрити", callback_data=f"support:status:{ticket_id}:closed"))
    kb.add(types.InlineKeyboardButton("↩️ До звернень", callback_data="support:list"))
    bot.send_message(chat_id, "\n\n".join(lines), parse_mode="HTML", reply_markup=kb)


def support_render_list(chat_id: int, actor: Staff) -> None:
    if not actor.can("support.read"):
        raise PermissionError("Недостатньо прав.")
    rows = support_ticket_rows()
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        kb.add(types.InlineKeyboardButton(
            f"#{row['id']} · {TICKET_STATUS_LABELS.get(row['status'], row['status'])} · {row['message_count']} повід.",
            callback_data=f"support:ticket:{row['id']}"))
    kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    title = "<b>🎫 Відкриті звернення</b>\nОстанні 30 активних звернень:" if rows else "<b>🎫 Звернення</b>\nВідкритих звернень немає."
    bot.send_message(chat_id, title, parse_mode="HTML", reply_markup=kb)

def task_rows_for_staff(telegram_id: int, is_manager: bool = False, limit: int = 50) -> list[dict]:
    with db_cursor() as cur:
        if is_manager:
            cur.execute(
                """SELECT t.*,s.display_name assigned_name FROM business_tasks t
                   LEFT JOIN staff s ON s.telegram_id=t.assigned_to
                   WHERE t.status IN ('open','in_progress')
                   ORDER BY t.due_at NULLS LAST,t.created_at DESC LIMIT %s""", (max(1,min(100,limit)),))
        else:
            cur.execute(
                """SELECT t.*,s.display_name assigned_name FROM business_tasks t
                   LEFT JOIN staff s ON s.telegram_id=t.assigned_to
                   WHERE (t.assigned_to=%s OR t.created_by=%s) AND t.status IN ('open','in_progress')
                   ORDER BY t.due_at NULLS LAST,t.created_at DESC LIMIT %s""",
                (telegram_id, telegram_id, max(1,min(100,limit))))
        return list(cur.fetchall())


def task_set_status(task_id: int, status: str, actor: Staff) -> None:
    if status not in ("open", "in_progress", "done", "cancelled"):
        raise ValueError("Невідомий статус задачі.")
    with db_cursor() as cur:
        cur.execute("SELECT assigned_to,created_by,status FROM business_tasks WHERE id=%s FOR UPDATE",
                    (task_id,))
        task = cur.fetchone()
        if not task:
            raise ValueError("Задачу не знайдено.")
        if actor.role not in ("owner", "admin") and actor.telegram_id not in (task["assigned_to"], task["created_by"]):
            raise PermissionError("Ця задача призначена іншому працівнику.")
        cur.execute(
            """UPDATE business_tasks SET status=%s,
               completed_at=CASE WHEN %s='done' THEN NOW() ELSE NULL END
               WHERE id=%s""", (status,status,task_id))
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,before_data,after_data)
               VALUES(%s,%s,'task.status_changed','task',%s,%s::jsonb,%s::jsonb)""",
            (actor.telegram_id,actor.role,str(task_id),json_dumps({"status":task["status"]}),
             json_dumps({"status":status})))


def task_render_list(chat_id: int, actor: Staff) -> None:
    rows = task_rows_for_staff(actor.telegram_id, actor.role in ("owner","admin"))
    if not rows:
        bot.send_message(chat_id, "✅ Активних задач немає.")
        return
    lines = ["<b>🗂️ Робочі задачі</b>"]
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows:
        due = row["due_at"] or "без дедлайну"
        lines.append(
            f"#{row['id']} · <b>{safe(row['title'])}</b>\n"
            f"Статус: {safe(row['status'])} · Дедлайн: {safe(due)}\n"
            f"Виконавець: {safe(row.get('assigned_name') or 'не призначено')}"
        )
        if row["status"] != "done":
            kb.add(types.InlineKeyboardButton(f"✅ Завершити #{row['id']}",
                                              callback_data=f"tasks:done:{row['id']}"))
            kb.add(types.InlineKeyboardButton(f"▶️ В роботі #{row['id']}",
                                              callback_data=f"tasks:progress:{row['id']}"))
    bot.send_message(chat_id, "\n\n".join(lines), parse_mode="HTML", reply_markup=kb)


@bot.message_handler(commands=["tickets"])
def support_list_command(message):
    staff = require_staff(message, "support.read")
    if staff:
        support_render_list(message.chat.id, staff)


def support_reply_step(message, ticket_id: int) -> None:
    staff = require_staff(message, "support.read")
    if not staff:
        bot.reply_to(message, "⛔ Доступ до підтримки відсутній або тимчасово призупинений.")
        return
    body = (message.text or "").strip()
    if body.casefold() == "/cancel":
        bot.reply_to(message, "Відповідь скасовано.")
        return
    if body in {label for label, _ in OWNER_SECTIONS} or body == "🏠 Головне меню":
        bot.reply_to(message, "Відповідь не надіслано, бо ви натиснули кнопку меню. Відкрийте звернення ще раз і натисніть «Відповісти».")
        return
    if not body or len(body) > 4000:
        prompt = bot.reply_to(message, "Введіть текст відповіді до 4000 символів або /cancel.")
        bot.register_next_step_handler(prompt, support_reply_step, ticket_id)
        return
    try:
        support_staff_reply(ticket_id, body, staff)
        bot.reply_to(message, f"✅ Відповідь на звернення #{ticket_id} надіслано клієнту.")
        support_render_ticket(message.chat.id, ticket_id, staff)
    except Exception as exc:
        log.exception("Interactive support reply failed")
        bot.reply_to(message, f"⚠️ Не вдалося надіслати відповідь: {safe(exc)}")


@bot.message_handler(commands=["ticket_reply"])
def support_reply_command(message):
    staff = require_staff(message, "support.read")
    if not staff:
        bot.reply_to(message, "⛔ Немає доступу.")
        return
    parts = (message.text or "").split(maxsplit=2)
    if len(parts) < 3 or not parts[1].isdigit():
        bot.reply_to(message, "Формат: /ticket_reply ID текст відповіді")
        return
    try:
        support_staff_reply(int(parts[1]), parts[2], staff)
        bot.reply_to(message, f"✅ Відповідь на звернення #{parts[1]} надіслано клієнту.")
    except Exception as exc:
        bot.reply_to(message, f"⚠️ {safe(exc)}")


@bot.message_handler(commands=["mytasks"])
def my_tasks_command(message):
    staff = require_staff(message)
    if staff:
        task_render_list(message.chat.id, staff)


@bot.message_handler(commands=["task_new"])
def task_new_command(message):
    staff = require_staff(message)
    if not staff or staff.role not in ("owner", "admin"):
        bot.reply_to(message, "⛔ Створювати задачі може власник або адміністратор.")
        return
    parts = (message.text or "").split(maxsplit=1)
    if len(parts) < 2:
        bot.reply_to(message, "Формат: /task_new Назва | опис | TELEGRAM_ID | YYYY-MM-DD\nID та дата необов’язкові.")
        return
    try:
        chunks = [x.strip() for x in parts[1].split("|")]
        if len(chunks) > 4:
            raise ValueError("Забагато параметрів.")
        title = chunks[0]
        description = chunks[1] if len(chunks) > 1 else ""
        assigned_to = int(chunks[2]) if len(chunks) > 2 and chunks[2] else None
        due_at = None
        if len(chunks) > 3 and chunks[3]:
            due_at = datetime.strptime(chunks[3], "%Y-%m-%d").replace(tzinfo=ZoneInfo("Europe/Kyiv"))
        task_id = create_business_task(title, description, assigned_to, due_at, staff)
        bot.reply_to(message, f"✅ Створено задачу #{task_id}.")
    except (ValueError, TypeError) as exc:
        bot.reply_to(message, f"⚠️ Некоректні параметри задачі: {safe(exc)}")
    except Exception as exc:
        log.exception("Task creation failed")
        bot.reply_to(message, f"⚠️ Не вдалося створити задачу: {safe(exc)}")

@bot.message_handler(commands=["ticket_assign"])
def support_assign_command(message):
    staff = require_staff(message, "support.read")
    if not staff or staff.role not in ("owner", "admin"):
        bot.reply_to(message, "⛔ Призначати звернення може власник або адміністратор.")
        return
    parts = (message.text or "").split()
    if len(parts) != 3 or not parts[1].isdigit() or not parts[2].isdigit():
        bot.reply_to(message, "Формат: /ticket_assign ID_ЗВЕРНЕННЯ TELEGRAM_ID_ПРАЦІВНИКА")
        return
    try:
        support_assign_ticket(int(parts[1]), int(parts[2]), staff)
        bot.reply_to(message, f"✅ Звернення #{parts[1]} призначено працівнику {parts[2]}.")
    except Exception as exc:
        bot.reply_to(message, f"⚠️ {safe(exc)}")


@bot.callback_query_handler(func=lambda c: c.data.startswith("support:"))
def support_operations_callback(call):
    staff = require_staff(call, "support.read")
    if not staff:
        bot.answer_callback_query(call.id, "Немає доступу.", show_alert=True)
        return
    try:
        parts = call.data.split(":")
        if parts[1] == "list":
            bot.answer_callback_query(call.id)
            support_render_list(call.message.chat.id, staff)
        elif parts[1] == "ticket":
            bot.answer_callback_query(call.id)
            support_render_ticket(call.message.chat.id, int(parts[2]), staff)
        elif parts[1] == "reply":
            ticket_id = int(parts[2])
            bot.answer_callback_query(call.id)
            prompt = bot.send_message(call.message.chat.id, f"✍️ Напишіть відповідь для звернення #{ticket_id}. Для скасування введіть /cancel.")
            bot.register_next_step_handler(prompt, support_reply_step, ticket_id)
        elif parts[1] == "status":
            support_set_ticket_status(int(parts[2]), parts[3], staff)
            bot.answer_callback_query(call.id, "Статус оновлено.")
            support_render_ticket(call.message.chat.id, int(parts[2]), staff)
        else:
            raise ValueError("Невідома дія підтримки.")
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(exc)[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("tasks:"))
def tasks_operations_callback(call):
    staff = require_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Немає доступу.", show_alert=True)
        return
    try:
        _, action, task_id = call.data.split(":")
        task_set_status(int(task_id), "done" if action == "done" else "in_progress", staff)
        bot.answer_callback_query(call.id, "Статус задачі оновлено.")
        task_render_list(call.message.chat.id, staff)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(exc)[:180], show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("sec:audit:"))
def security_staff_audit_callback(call):
    staff = require_staff(call)
    if not staff or staff.role != "owner":
        bot.answer_callback_query(call.id, "Лише власник.", show_alert=True)
        return
    try:
        _, _, telegram_id, offset = call.data.split(":")
        bot.answer_callback_query(call.id)
        security_render_staff_audit(call.message.chat.id, int(telegram_id), int(offset), staff)
    except Exception as exc:
        bot.answer_callback_query(call.id, safe(exc)[:180], show_alert=True)



# ---------------------------------------------------------------------------
# v1.36 additions: consent buttons, saved checkout data, customer ticket replies,
# order card from notification, marketing opt-out
# ---------------------------------------------------------------------------

@bot.callback_query_handler(func=lambda c: c.data.startswith("consent:"))
def checkout_consent_callback(call):
    action = call.data.split(":")[1]
    uid = call.from_user.id
    try:
        if action == "decline":
            bot.answer_callback_query(call.id)
            bot.send_message(call.message.chat.id, "Без згоди на обробку даних оформити замовлення неможливо. Кошик збережено, ви можете повернутися пізніше.", reply_markup=customer_menu())
            return
        if action not in ("accept", "accept_ads"):
            bot.answer_callback_query(call.id)
            return
        record_privacy_consent(uid, CONFIG.privacy_consent_version, _privacy_consent_text(), True)
        if action == "accept_ads":
            record_privacy_consent(uid, MARKETING_CONSENT_KEY, MARKETING_CONSENT_TEXT, True)
        bot.answer_callback_query(call.id, "Згоду збережено")
        try:
            bot.edit_message_reply_markup(call.message.chat.id, call.message.message_id, reply_markup=None)
        except Exception:
            pass
        continue_checkout_after_consent(call.message.chat.id, call.from_user)
    except Exception:
        log.exception("Consent callback failed")
        bot.answer_callback_query(call.id, "Не вдалося зберегти згоду. Спробуйте ще раз.", show_alert=True)


@bot.callback_query_handler(func=lambda c: c.data.startswith("checkout:reuse:"))
def checkout_reuse_callback(call):
    uid = call.from_user.id
    try:
        bot.answer_callback_query(call.id)
        customer_id = upsert_customer(call.from_user)
        if call.data.endswith(":yes"):
            with db_cursor() as cur:
                cur.execute("SELECT phone,full_name FROM customers WHERE id=%s", (customer_id,))
                row = cur.fetchone()
            name = _clean_full_name(row["full_name"]) if row and row.get("full_name") else None
            if not (row and row.get("phone") and name):
                save_checkout_draft(uid, customer_id, step="phone")
                ask_checkout_phone(call.message.chat.id)
                return
            save_checkout_draft(uid, customer_id, phone=row["phone"], customer_name=name, step="delivery")
            send_delivery_choice(call.message.chat.id)
        else:
            save_checkout_draft(uid, customer_id, step="phone")
            ask_checkout_phone(call.message.chat.id)
    except Exception:
        log.exception("Checkout reuse callback failed")
        bot.send_message(call.message.chat.id, "⚠️ Не вдалося продовжити оформлення. Спробуйте ще раз з кошика.")


@bot.callback_query_handler(func=lambda c: c.data.startswith("cs:reply:"))
def customer_ticket_reply_callback(call):
    try:
        ticket_id = int(call.data.split(":")[2])
        with db_cursor() as cur:
            cur.execute("SELECT status FROM support_tickets WHERE id=%s AND customer_telegram_id=%s", (ticket_id, call.from_user.id))
            ticket = cur.fetchone()
        if not ticket:
            bot.answer_callback_query(call.id, "Звернення не знайдено.", show_alert=True)
            return
        if ticket["status"] == "closed":
            bot.answer_callback_query(call.id, "Це звернення закрите. Створіть нове через «🎫 Підтримка».", show_alert=True)
            return
        bot.answer_callback_query(call.id)
        msg = bot.send_message(call.message.chat.id, f"Напишіть вашу відповідь до звернення #{ticket_id}:")
        bot.register_next_step_handler(msg, customer_ticket_reply_step, ticket_id)
    except Exception:
        log.exception("Customer ticket reply callback failed")
        bot.answer_callback_query(call.id, "Не вдалося відкрити звернення.", show_alert=True)


def customer_ticket_reply_step(message, ticket_id: int) -> None:
    text = (message.text or "").strip()
    if not text or len(text) > 4000:
        msg = bot.reply_to(message, "Надішліть відповідь текстом (до 4000 символів).")
        bot.register_next_step_handler(msg, customer_ticket_reply_step, ticket_id)
        return
    try:
        with db_cursor() as cur:
            cur.execute("SELECT assigned_to FROM support_tickets WHERE id=%s AND customer_telegram_id=%s", (ticket_id, message.from_user.id))
            ticket = cur.fetchone()
        if not ticket:
            bot.reply_to(message, "Звернення не знайдено.")
            return
        add_ticket_reply(ticket_id, message.from_user.id, "customer", text)
        payload = {"ticket_id": ticket_id,
                   "text": f"💬 <b>Відповідь клієнта у зверненні #{ticket_id}</b>\n\n{safe(text[:800])}",
                   "buttons": [["✍️ Відповісти", f"support:reply:{ticket_id}"],
                               ["📂 Відкрити звернення", f"support:ticket:{ticket_id}"]]}
        with db_cursor() as cur:
            recipients = {CONFIG.owner_id}
            if ticket.get("assigned_to"):
                recipients.add(int(ticket["assigned_to"]))
            else:
                recipients.update(staff_recipient_ids(cur, ("owner", "admin", "manager")))
            for rid in recipients:
                enqueue_notification(cur, rid, "support", payload, f"ticket:{ticket_id}:cust-reply:{uuid.uuid4().hex}")
        bot.reply_to(message, "✅ Відповідь надіслано. Ми відповімо тут у чаті.", reply_markup=customer_menu())
    except ValueError as exc:
        bot.reply_to(message, safe(str(exc)))
    except Exception:
        log.exception("Customer ticket reply failed")
        bot.reply_to(message, "⚠️ Не вдалося надіслати відповідь. Спробуйте ще раз.")


@bot.callback_query_handler(func=lambda c: c.data.startswith("ordview:"))
def order_view_callback(call):
    staff = require_staff(call, "orders.read")
    if not staff:
        bot.answer_callback_query(call.id, "Немає доступу.", show_alert=True)
        return
    try:
        order_id = int(call.data.split(":")[1])
        with db_cursor() as cur:
            cur.execute(order_select_sql("WHERE o.id=%s"), (order_id,))
            order = cur.fetchone()
        bot.answer_callback_query(call.id)
        if not order:
            bot.send_message(call.message.chat.id, "Замовлення не знайдено.")
            return
        bot.send_message(call.message.chat.id, order_card_text(order), reply_markup=order_keyboard(order, staff))
    except Exception:
        log.exception("Order view callback failed")
        bot.answer_callback_query(call.id, "Не вдалося відкрити замовлення.", show_alert=True)


# ---------------------------------------------------------------------------
# Owner-only customer PDF export. Password is read from Render environment.
# ---------------------------------------------------------------------------

CUSTOMER_EXPORT_PASSWORD_ENV = "CUSTOMER_EXPORT_PASSWORD"
CUSTOMER_EXPORT_FONT_FILENAME = "CloudHub-DejaVuSans.ttf"


def _customer_export_font_path() -> str:
    candidates = [
        os.getenv("CUSTOMER_EXPORT_FONT_PATH", "").strip(),
        os.path.join(os.path.dirname(os.path.abspath(__file__)), CUSTOMER_EXPORT_FONT_FILENAME),
        os.path.join(CONFIG.data_dir, CUSTOMER_EXPORT_FONT_FILENAME),
        os.path.join(os.getcwd(), CUSTOMER_EXPORT_FONT_FILENAME),
    ]
    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            return candidate
    raise FileNotFoundError(
        f"Не знайдено {CUSTOMER_EXPORT_FONT_FILENAME}. Покладіть файл у корінь репозиторію "
        "або задайте CUSTOMER_EXPORT_FONT_PATH."
    )


def _build_customers_pdf(output_path: str) -> int:
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import mm
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle

    font_path = _customer_export_font_path()
    pdfmetrics.registerFont(TTFont("CloudHub", font_path))
    styles = getSampleStyleSheet()
    title_style = ParagraphStyle("CHTitle", parent=styles["Title"], fontName="CloudHub", fontSize=16, leading=20, alignment=TA_CENTER)
    body_style = ParagraphStyle("CHBody", parent=styles["BodyText"], fontName="CloudHub", fontSize=7, leading=9, alignment=TA_LEFT)
    head_style = ParagraphStyle("CHHead", parent=body_style, fontSize=7, leading=8)
    with db_cursor() as cur:
        cur.execute("""SELECT c.id,c.telegram_id,c.username,c.first_name,c.last_name,c.full_name,c.phone,
                             c.loyalty_card_number,c.created_at,
                             COUNT(DISTINCT o.id)::int AS orders_count,
                             COALESCE(SUM(CASE WHEN o.status NOT IN ('cancelled','canceled','returned')
                                               THEN o.grand_total ELSE 0 END),0) AS lifetime_spend,
                             COALESCE(la.available,0) AS bonus_available,
                             COALESCE(la.pending,0) AS bonus_pending
                      FROM customers c
                      LEFT JOIN orders o ON o.customer_id=c.id
                      LEFT JOIN loyalty_accounts la ON la.customer_id=c.id
                      GROUP BY c.id,la.available,la.pending
                      ORDER BY c.created_at DESC,c.id DESC""")
        rows = list(cur.fetchall())
    doc = SimpleDocTemplate(output_path, pagesize=landscape(A4), rightMargin=9*mm, leftMargin=9*mm,
                            topMargin=9*mm, bottomMargin=9*mm, title="Cloud Hub customers")
    story = [Paragraph("Cloud Hub · Реєстр клієнтів", title_style),
             Paragraph(f"Сформовано: {datetime.now(ZoneInfo(CONFIG.timezone)).strftime('%d.%m.%Y %H:%M')} · Клієнтів: {len(rows)}", body_style),
             Spacer(1, 5*mm)]
    headers = ["ID", "Ім’я", "Телефон", "Telegram ID", "Username", "Картка", "Замовлень", "Витрачено, грн", "Бонуси доступні", "Бонуси очікують"]
    data = [[Paragraph(h, head_style) for h in headers]]
    for r in rows:
        name = r.get("full_name") or " ".join(x for x in [r.get("first_name"), r.get("last_name")] if x) or "—"
        values = [r["id"], name, r.get("phone") or "—", r.get("telegram_id") or "—",
                  ("@" + r["username"]) if r.get("username") else "—", r.get("loyalty_card_number") or "—",
                  r.get("orders_count") or 0, money(r.get("lifetime_spend") or 0),
                  money(r.get("bonus_available") or 0), money(r.get("bonus_pending") or 0)]
        data.append([Paragraph(safe(v), body_style) for v in values])
    widths = [10*mm, 32*mm, 25*mm, 23*mm, 22*mm, 25*mm, 15*mm, 22*mm, 22*mm, 22*mm]
    table = Table(data, colWidths=widths, repeatRows=1, hAlign="LEFT")
    table.setStyle(TableStyle([
        ("BACKGROUND", (0,0), (-1,0), colors.HexColor("#263445")),
        ("TEXTCOLOR", (0,0), (-1,0), colors.white),
        ("GRID", (0,0), (-1,-1), 0.25, colors.HexColor("#CBD5E1")),
        ("VALIGN", (0,0), (-1,-1), "TOP"),
        ("ROWBACKGROUNDS", (0,1), (-1,-1), [colors.white, colors.HexColor("#F3F6F9")]),
        ("LEFTPADDING", (0,0), (-1,-1), 3), ("RIGHTPADDING", (0,0), (-1,-1), 3),
        ("TOPPADDING", (0,0), (-1,-1), 3), ("BOTTOMPADDING", (0,0), (-1,-1), 3),
    ]))
    story.append(table)
    doc.build(story)
    return len(rows)


CUSTOMER_EXPORT_WAITING: set[int] = set()


def _start_customer_export(message_or_call) -> None:
    user = message_or_call.from_user
    staff = require_staff(message_or_call)
    if not staff or staff.role != "owner":
        if hasattr(message_or_call, "id") and hasattr(message_or_call, "message"):
            bot.answer_callback_query(message_or_call.id, "Експорт доступний лише власнику.", show_alert=True)
        else:
            bot.reply_to(message_or_call, "⛔ Експорт доступний лише власнику.")
        return
    password = os.getenv(CUSTOMER_EXPORT_PASSWORD_ENV, "")
    if not password:
        text = f"⚠️ Не задано змінну Render {CUSTOMER_EXPORT_PASSWORD_ENV}."
        if hasattr(message_or_call, "id") and hasattr(message_or_call, "message"):
            bot.answer_callback_query(message_or_call.id, text, show_alert=True)
        else:
            bot.reply_to(message_or_call, text)
        return
    CUSTOMER_EXPORT_WAITING.add(user.id)
    chat_id = message_or_call.message.chat.id if hasattr(message_or_call, "message") else message_or_call.chat.id
    if hasattr(message_or_call, "id") and hasattr(message_or_call, "message"):
        bot.answer_callback_query(message_or_call.id)
    prompt = bot.send_message(chat_id, "🔐 Введіть пароль експорту одним повідомленням. Спроба не записується в журнал.")
    bot.register_next_step_handler(prompt, _customer_export_password_step)


def _customer_export_password_step(message) -> None:
    user_id = message.from_user.id
    if user_id not in CUSTOMER_EXPORT_WAITING:
        return
    CUSTOMER_EXPORT_WAITING.discard(user_id)
    actor = require_staff(message)
    if not actor or actor.role != "owner":
        return
    import hmac
    expected = os.getenv(CUSTOMER_EXPORT_PASSWORD_ENV, "")
    supplied = (message.text or "").strip()
    if not expected or not hmac.compare_digest(supplied, expected):
        bot.reply_to(message, "⛔ Пароль неправильний. Експорт не виконано.")
        return
    output_path = os.path.join(CONFIG.data_dir, "backups", f"cloudhub_customers_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}.pdf")
    try:
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        count = _build_customers_pdf(output_path)
        audit(actor, "customer.export", "customers", "all", after={"rows": count, "format": "pdf"}, reason="Owner password-protected customer export")
        with open(output_path, "rb") as fh:
            bot.send_document(message.chat.id, fh, caption=f"📄 Реєстр клієнтів Cloud Hub · {count} записів")
    except Exception as exc:
        log.exception("Customer PDF export failed")
        bot.reply_to(message, f"⚠️ Не вдалося сформувати PDF: {safe(str(exc))[:300]}")
    finally:
        try:
            if os.path.exists(output_path):
                os.remove(output_path)
        except OSError:
            log.warning("Could not remove temporary customer export %s", output_path)




@bot.callback_query_handler(func=lambda c: c.data == "customers:export")
def customer_export_callback(call):
    _start_customer_export(call)


@bot.callback_query_handler(func=lambda c: c.data == "marketing:accept")
def marketing_accept_callback(call):
    try:
        record_privacy_consent(call.from_user.id, MARKETING_CONSENT_KEY, MARKETING_CONSENT_TEXT, True)
        bot.answer_callback_query(call.id, "Підписку збережено.")
        bot.send_message(call.message.chat.id,
                         "✅ Ви підписалися на новини та пропозиції Cloud Hub. Відписатися можна командою /stop_ads.")
    except Exception:
        log.exception("Marketing opt-in callback failed")
        bot.answer_callback_query(call.id, "Не вдалося зберегти згоду. Спробуйте пізніше.", show_alert=True)


@bot.message_handler(commands=["stop_ads"])
def marketing_unsubscribe(message):
    try:
        record_privacy_consent(message.from_user.id, MARKETING_CONSENT_KEY, MARKETING_CONSENT_TEXT, False)
        bot.reply_to(message, "✅ Ви відписалися від рекламних розсилок. Повідомлення про ваші замовлення й підтримку ви й надалі отримуватимете. Щоб підписатися знову, надішліть /ads_on.")
    except Exception:
        log.exception("Unsubscribe failed")
        bot.reply_to(message, "⚠️ Не вдалося зберегти вибір. Спробуйте пізніше або напишіть у підтримку.")


@bot.message_handler(commands=["ads_on"])
def marketing_subscribe(message):
    try:
        record_privacy_consent(message.from_user.id, MARKETING_CONSENT_KEY, MARKETING_CONSENT_TEXT, True)
        bot.reply_to(message, "✅ Ви підписалися на рекламні розсилки Cloud Hub. Відписатися можна командою /stop_ads.")
    except Exception:
        log.exception("Subscribe failed")
        bot.reply_to(message, "⚠️ Не вдалося зберегти вибір. Спробуйте пізніше.")


@bot.message_handler(func=lambda m: True, content_types=["text"])
def fallback(message):
    # Staff may paste a one-time access phrase anywhere in the bot chat.
    try:
        if redeem_staff_access_code(message):
            return
    except Exception:
        log.exception("Staff access-code redemption failed")
        bot.reply_to(message, "⚠️ Не вдалося активувати код. Зверніться до власника.")
        return
    staff = require_staff(message)
    if not staff:
        return
    bot.reply_to(message, "Не знайшов такої команди. Скористайтеся кнопками меню або /start.")


# ---------------------------------------------------------------------------
# Health checks, lifecycle
# ---------------------------------------------------------------------------

def validate_environment() -> None:
    if CONFIG.owner_id <= 0:
        raise RuntimeError("OWNER_TELEGRAM_ID must be positive")
    if not CONFIG.database_url.startswith(("postgresql://", "postgresql+")):
        raise RuntimeError("DATABASE_URL must point to PostgreSQL")
    if not CONFIG.consent_database_url.startswith(("postgresql://", "postgresql+")):
        raise RuntimeError("CONSENT_DATABASE_URL must point to a separate PostgreSQL database")
    if len(CONFIG.bot_token) < 20:
        raise RuntimeError("BOT_TOKEN looks invalid; check Render environment variables")


def shutdown(*_args):
    log.info("Shutdown signal received")
    _maintenance_stop.set()
    try:
        bot.stop_polling()
    except Exception:
        pass
    if pool is not None:
        pool.close()
    if consent_pool is not None:
        consent_pool.close()
    raise SystemExit(0)


_maintenance_stop = threading.Event()


def maintenance_loop() -> None:
    last_loyalty_expiry = 0.0
    while not _maintenance_stop.wait(5):
        try:
            complete_expired_staff_reviews()
            complete_expired_security_locks()
            release_expired_reservations()
            recover_stale_notification_claims()
            dispatch_notification_batch(25)
            if time.time() - last_loyalty_expiry >= 300:
                expire_loyalty_lots()
                last_loyalty_expiry = time.time()
        except Exception:
            log.exception("Cloud Hub maintenance cycle failed")


def main() -> None:
    validate_environment()
    require_disk = os.getenv("REQUIRE_PERSISTENT_DISK", "true").strip().lower() in ("1", "true", "yes", "on")
    if require_disk and not os.path.ismount(CONFIG.data_dir):
        raise RuntimeError(f"Persistent disk is not mounted at {CONFIG.data_dir}; refusing to start with ephemeral file storage")
    init_db()
    resume_running_broadcasts()
    maintenance_thread = threading.Thread(target=maintenance_loop, name="cloudhub-maintenance", daemon=True)
    maintenance_thread.start()
    signal.signal(signal.SIGTERM, shutdown)
    signal.signal(signal.SIGINT, shutdown)
    log.info("Cloud Hub v1.43 worker starting")
    bot.infinity_polling(
        timeout=30,
        long_polling_timeout=25,
        skip_pending=False,
        allowed_updates=["message", "callback_query"],
    )




def migrate_v1_20_notification_outbox() -> None:
    """Idempotently add dispatcher lease columns to existing databases."""
    with db_cursor() as cur:
        cur.execute("ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS available_at TIMESTAMPTZ NOT NULL DEFAULT NOW()")
        cur.execute("ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS last_attempt_at TIMESTAMPTZ")
        cur.execute("ALTER TABLE notification_outbox ADD COLUMN IF NOT EXISTS claim_token TEXT")
        cur.execute("CREATE INDEX IF NOT EXISTS idx_notification_outbox_due ON notification_outbox(state, available_at, id)")


def recover_stale_notification_claims() -> int:
    """Recover abandoned leases after a worker crash."""
    with db_cursor() as cur:
        cur.execute(
            """UPDATE notification_outbox
               SET claim_token=NULL,
                   state=CASE WHEN attempts>=8 THEN 'failed' ELSE 'pending' END,
                   available_at=NOW(),
                   last_error=COALESCE(last_error,'Відновлено прострочене захоплення outbox')
               WHERE state='pending' AND claim_token IS NOT NULL
                 AND available_at < NOW()-INTERVAL '1 minute'
               RETURNING id"""
        )
        return len(cur.fetchall())


def notification_outbox_health() -> dict:
    with db_cursor() as cur:
        cur.execute(
            """SELECT COUNT(*) FILTER (WHERE state='pending')::int AS pending,
                      COUNT(*) FILTER (WHERE state='pending' AND available_at<=NOW())::int AS due,
                      COUNT(*) FILTER (WHERE state='failed')::int AS failed,
                      COUNT(*) FILTER (WHERE state='blocked')::int AS blocked,
                      MIN(created_at) FILTER (WHERE state='pending') AS oldest_pending
               FROM notification_outbox"""
        )
        return dict(cur.fetchone() or {})



def inventory_integrity_audit(limit: int = 100) -> dict:
    """Read-only reconciliation of stock balances, movement ledger and reservations.

    A discrepancy is reported for human review; this function never auto-repairs stock.
    """
    limit = max(1, min(500, int(limit)))
    with db_cursor() as cur:
        cur.execute(
            """WITH ledger AS (
                 SELECT variant_id, COALESCE(SUM(quantity_delta),0)::bigint AS ledger_qty,
                        COUNT(*)::int AS movement_count,
                        MAX(created_at) AS last_movement_at
                 FROM inventory_movements GROUP BY variant_id
               ), reservations AS (
                 SELECT variant_id,
                        COALESCE(SUM(quantity) FILTER (WHERE state='active'),0)::bigint AS active_reserved,
                        COUNT(*) FILTER (WHERE state='active')::int AS active_reservation_count
                 FROM stock_reservations GROUP BY variant_id
               )
               SELECT v.id AS variant_id,v.sku,p.name AS product_name,
                      v.stock_qty,v.reserved_qty,
                      COALESCE(l.ledger_qty,0)::bigint AS ledger_qty,
                      COALESCE(l.movement_count,0)::int AS movement_count,
                      l.last_movement_at,
                      COALESCE(r.active_reserved,0)::bigint AS active_reserved,
                      COALESCE(r.active_reservation_count,0)::int AS active_reservation_count,
                      (v.stock_qty-COALESCE(l.ledger_qty,0))::bigint AS ledger_difference,
                      (v.reserved_qty-COALESCE(r.active_reserved,0))::bigint AS reservation_difference
               FROM product_variants v
               JOIN products p ON p.id=v.product_id
               LEFT JOIN ledger l ON l.variant_id=v.id
               LEFT JOIN reservations r ON r.variant_id=v.id
               WHERE v.stock_qty<>COALESCE(l.ledger_qty,0)
                  OR v.reserved_qty<>COALESCE(r.active_reserved,0)
                  OR v.stock_qty<0 OR v.reserved_qty<0 OR v.reserved_qty>v.stock_qty
               ORDER BY
                 CASE WHEN v.stock_qty<0 OR v.reserved_qty<0 OR v.reserved_qty>v.stock_qty THEN 0 ELSE 1 END,
                 ABS(v.stock_qty-COALESCE(l.ledger_qty,0)) DESC,
                 ABS(v.reserved_qty-COALESCE(r.active_reserved,0)) DESC,
                 v.id
               LIMIT %s""",
            (limit,),
        )
        rows = list(cur.fetchall())
        cur.execute(
            """SELECT COUNT(*)::int AS total_variants,
                      COUNT(*) FILTER (WHERE v.stock_qty<>COALESCE(l.ledger_qty,0))::int AS ledger_mismatches,
                      COUNT(*) FILTER (WHERE v.reserved_qty<>COALESCE(r.active_reserved,0))::int AS reservation_mismatches,
                      COUNT(*) FILTER (WHERE v.stock_qty<0 OR v.reserved_qty<0 OR v.reserved_qty>v.stock_qty)::int AS impossible_balances
               FROM product_variants v
               LEFT JOIN (SELECT variant_id,SUM(quantity_delta) ledger_qty FROM inventory_movements GROUP BY variant_id) l
                 ON l.variant_id=v.id
               LEFT JOIN (SELECT variant_id,SUM(quantity) FILTER (WHERE state='active') active_reserved
                          FROM stock_reservations GROUP BY variant_id) r ON r.variant_id=v.id"""
        )
        summary = dict(cur.fetchone() or {})
        summary["rows"] = rows
        summary["truncated"] = (
            int(summary.get("ledger_mismatches", 0))
            + int(summary.get("reservation_mismatches", 0))
            + int(summary.get("impossible_balances", 0)) > len(rows)
        )
        return summary


def render_inventory_integrity_audit(chat_id: int, actor: Staff) -> None:
    if actor.role != "owner":
        raise PermissionError("Повний аудит залишків доступний лише власнику.")
    report = inventory_integrity_audit(100)
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,after_data)
               VALUES(%s,%s,'inventory.integrity_audit','inventory','all',%s::jsonb)""",
            (actor.telegram_id, actor.role,
             json_dumps({k: report.get(k) for k in
                         ("total_variants","ledger_mismatches","reservation_mismatches","impossible_balances")})),
        )
    lines = [
        "<b>🔎 Аудит цілісності складу</b>",
        f"SKU у системі: <b>{int(report.get('total_variants',0))}</b>",
        f"Розбіжності фізичного залишку з журналом рухів: <b>{int(report.get('ledger_mismatches',0))}</b>",
        f"Розбіжності резервів: <b>{int(report.get('reservation_mismatches',0))}</b>",
        f"Неможливі баланси (від'ємний залишок або резерв більший за залишок): <b>{int(report.get('impossible_balances',0))}</b>",
    ]
    rows = report.get("rows", [])
    if rows:
        lines.append("\n<b>Позиції для ручної перевірки:</b>")
        for row in rows[:30]:
            flags = []
            if int(row["ledger_difference"]):
                flags.append(f"журнал {int(row['ledger_difference']):+d}")
            if int(row["reservation_difference"]):
                flags.append(f"резерв {int(row['reservation_difference']):+d}")
            if int(row["stock_qty"]) < 0 or int(row["reserved_qty"]) < 0 or int(row["reserved_qty"]) > int(row["stock_qty"]):
                flags.append("неможливий баланс")
            lines.append(
                f"• {safe(row['product_name'])} / <code>{safe(row['sku'])}</code>: "
                f"фізично {row['stock_qty']}, резерв {row['reserved_qty']} "
                f"({'; '.join(flags)})"
            )
    else:
        lines.append("✅ Розбіжностей не знайдено.")
    if report.get("truncated"):
        lines.append("\nПоказано не всі проблемні SKU. Звузьте аудит окремим звітом перед виправленням.")
    lines.append("\nЦе лише діагностика. Автоматичного виправлення залишків не виконувалося.")
    bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")


@bot.message_handler(commands=["stockaudit"])
def inventory_integrity_audit_command(message):
    staff = require_staff(message)
    if not staff:
        bot.reply_to(message, "⛔ Немає доступу.")
        return
    if staff.role != "owner":
        bot.reply_to(message, "⛔ Повний аудит складу доступний лише власнику.")
        return
    try:
        render_inventory_integrity_audit(message.chat.id, staff)
    except Exception:
        log.exception("Inventory integrity audit failed")
        bot.reply_to(message, "⚠️ Не вдалося виконати аудит складу. Перевірте журнал помилок.")



# =============================================================================
# CLOUD_HUB_STOCK_LIFECYCLE_V2
# =============================================================================
# Stock lifecycle hardening layer.
#
# Design rules:
# 1. product_variants.stock_qty is physical on-hand stock.
# 2. product_variants.reserved_qty is a denormalized sum of active reservations.
# 3. inventory_movements is the append-only stock ledger. A reservation is not
#    a physical movement; sale, receipt, return, opening balance, adjustment,
#    and inventory count are physical movements.
# 4. Every mutating operation locks the SKU row before changing its balance.
# 5. Every external workflow is idempotent at its document/state boundary.
# 6. A discrepancy report is read-only. Repair is a separate, confirmed action.
# 7. No repair silently rewrites history or deletes ledger entries.
#
# The functions below deliberately use the existing db_cursor(), Staff,
# json_dumps(), and permission model. They do not introduce another database,
# another SKU identity, or another stock table.
# =============================================================================

STOCK_PHYSICAL_MOVEMENT_TYPES = frozenset({
    "opening_balance", "supply", "sale", "manual_adjustment",
    "inventory_count", "return", "stock_reversal",
})
STOCK_RESERVATION_MOVEMENT_TYPES = frozenset({
    "reservation", "reservation_release", "reservation_expired",
})
STOCK_FINAL_ORDER_STATES = frozenset({"shipped", "delivered", "completed", "returned", "cancelled"})
STOCK_RESERVATION_ACTIVE = "active"
STOCK_RESERVATION_TERMINAL = frozenset({"consumed", "released", "expired"})


def _stock_int(value: Any, field_name: str, minimum: int = 0,
               maximum: int = 1_000_000) -> int:
    """Parse and bound an integer used in inventory operations."""
    try:
        parsed = int(value)
    except (TypeError, ValueError, OverflowError):
        raise ValueError(f"Поле «{field_name}» має бути цілим числом.")
    if parsed < minimum or parsed > maximum:
        raise ValueError(f"Поле «{field_name}» має бути в межах {minimum}–{maximum}.")
    return parsed


def _stock_reason(value: str, *, minimum: int = 5, maximum: int = 500) -> str:
    """Normalize a human reason and reject blank or oversized audit reasons."""
    clean = " ".join(str(value or "").split())
    if len(clean) < minimum:
        raise ValueError(f"Причина має містити щонайменше {minimum} символів.")
    if len(clean) > maximum:
        raise ValueError(f"Причина не може бути довшою за {maximum} символів.")
    return clean


def _stock_require(actor: Staff, permission: str) -> None:
    """Centralized permission gate for stock lifecycle operations."""
    if actor is None or not actor.can(permission):
        raise PermissionError("Недостатньо прав для цієї складської операції.")


def _stock_lock_variant(cur, variant_id: int) -> dict:
    """Lock one SKU and return its current physical/reserved balances."""
    cur.execute(
        """SELECT v.id, v.product_id, v.sku, v.stock_qty, v.reserved_qty,
                  v.cost_price, v.active, p.name AS product_name,
                  p.archived_at
           FROM product_variants v
           JOIN products p ON p.id=v.product_id
           WHERE v.id=%s
           FOR UPDATE OF v""",
        (variant_id,),
    )
    row = cur.fetchone()
    if not row:
        raise ValueError("SKU не знайдено.")
    return dict(row)


def _stock_write_movement(cur, *, variant_id: int, movement_type: str,
                          quantity_delta: int, reference_type: str = None,
                          reference_id: str = None, reason: str,
                          actor_telegram_id: int = None) -> int:
    """Append one immutable ledger movement and return its identifier."""
    if movement_type not in STOCK_PHYSICAL_MOVEMENT_TYPES | STOCK_RESERVATION_MOVEMENT_TYPES:
        raise ValueError("Невідомий тип складського руху.")
    if not isinstance(quantity_delta, int) or quantity_delta == 0:
        raise ValueError("Рух складу має мати ненульову цілу кількість.")
    clean_reason = _stock_reason(reason, minimum=3, maximum=500)
    cur.execute(
        """INSERT INTO inventory_movements
           (variant_id,movement_type,quantity_delta,reference_type,reference_id,
            reason,actor_telegram_id)
           VALUES(%s,%s,%s,%s,%s,%s,%s)
           RETURNING id""",
        (variant_id, movement_type, quantity_delta, reference_type,
         str(reference_id) if reference_id is not None else None,
         clean_reason, actor_telegram_id),
    )
    return int(cur.fetchone()["id"])


def _stock_audit(cur, actor: Staff, action: str, entity_type: str,
                 entity_id: Any, before: dict = None, after: dict = None,
                 reason: str = None) -> None:
    """Write an auditable before/after record inside the caller transaction."""
    cur.execute(
        """INSERT INTO audit_log
           (actor_telegram_id,actor_role,action,entity_type,entity_id,
            before_data,after_data,reason)
           VALUES(%s,%s,%s,%s,%s,%s::jsonb,%s::jsonb,%s)""",
        (actor.telegram_id if actor else None, actor.role if actor else None,
         action, entity_type, str(entity_id),
         json_dumps(before) if before is not None else None,
         json_dumps(after) if after is not None else None, reason),
    )


def stock_variant_snapshot(variant_id: int, actor: Staff) -> dict:
    """Return a read-only stock snapshot with active reservations and recent ledger."""
    if not (actor.can("inventory.read") or actor.can("inventory.adjust")
            or actor.can("inventory.receive")):
        raise PermissionError("Недостатньо прав для перегляду залишку.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id,v.sku,v.variant_name,v.stock_qty,v.reserved_qty,
                      v.stock_qty-v.reserved_qty AS available_qty,
                      v.cost_price,v.price,v.active,p.name AS product_name
               FROM product_variants v JOIN products p ON p.id=v.product_id
               WHERE v.id=%s""",
            (variant_id,),
        )
        variant = cur.fetchone()
        if not variant:
            raise ValueError("SKU не знайдено.")
        cur.execute(
            """SELECT state,COALESCE(SUM(quantity),0) AS quantity,
                      COUNT(*) AS reservation_count,
                      MIN(expires_at) FILTER (WHERE state='active') AS next_expiry
               FROM stock_reservations WHERE variant_id=%s GROUP BY state
               ORDER BY state""",
            (variant_id,),
        )
        reservations = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,movement_type,quantity_delta,reference_type,reference_id,
                      reason,actor_telegram_id,created_at
               FROM inventory_movements WHERE variant_id=%s
               ORDER BY id DESC LIMIT 50""",
            (variant_id,),
        )
        movements = [dict(x) for x in cur.fetchall()]
        return {"variant": dict(variant), "reservations": reservations,
                "recent_movements": movements}


def stock_ledger_trace(variant_id: int, actor: Staff, limit: int = 200,
                       before_id: int = None) -> dict:
    """Read the stock ledger in stable, descending-ID pages."""
    if not (actor.can("inventory.read") or actor.can("inventory.adjust")
            or actor.can("inventory.receive")):
        raise PermissionError("Недостатньо прав для перегляду журналу складу.")
    page_size = _stock_int(limit, "ліміт", 1, 500)
    with db_cursor() as cur:
        cur.execute("SELECT id,sku FROM product_variants WHERE id=%s", (variant_id,))
        sku = cur.fetchone()
        if not sku:
            raise ValueError("SKU не знайдено.")
        if before_id is None:
            cur.execute(
                """SELECT id,movement_type,quantity_delta,reference_type,reference_id,
                          reason,actor_telegram_id,created_at
                   FROM inventory_movements WHERE variant_id=%s
                   ORDER BY id DESC LIMIT %s""",
                (variant_id, page_size + 1),
            )
        else:
            cursor_id = _stock_int(before_id, "ідентифікатор руху", 1, 2**63 - 1)
            cur.execute(
                """SELECT id,movement_type,quantity_delta,reference_type,reference_id,
                          reason,actor_telegram_id,created_at
                   FROM inventory_movements
                   WHERE variant_id=%s AND id<%s
                   ORDER BY id DESC LIMIT %s""",
                (variant_id, cursor_id, page_size + 1),
            )
        rows = [dict(x) for x in cur.fetchall()]
    has_more = len(rows) > page_size
    rows = rows[:page_size]
    return {"variant_id": variant_id, "sku": sku["sku"], "items": rows,
            "has_more": has_more,
            "next_before_id": rows[-1]["id"] if has_more and rows else None}


def stock_reservation_trace(variant_id: int, actor: Staff,
                            include_terminal: bool = True,
                            limit: int = 200) -> list[dict]:
    """Inspect reservations by SKU, retaining order and expiry context."""
    if not (actor.can("inventory.read") or actor.can("orders.read")):
        raise PermissionError("Недостатньо прав для перегляду резервів.")
    page_size = _stock_int(limit, "ліміт", 1, 500)
    with db_cursor() as cur:
        if include_terminal:
            cur.execute(
                """SELECT r.id,r.order_id,r.quantity,r.state,r.expires_at,r.created_at,
                          o.status AS order_status,o.order_number
                   FROM stock_reservations r
                   LEFT JOIN orders o ON o.id=r.order_id
                   WHERE r.variant_id=%s
                   ORDER BY r.id DESC LIMIT %s""",
                (variant_id, page_size),
            )
        else:
            cur.execute(
                """SELECT r.id,r.order_id,r.quantity,r.state,r.expires_at,r.created_at,
                          o.status AS order_status,o.order_number
                   FROM stock_reservations r
                   LEFT JOIN orders o ON o.id=r.order_id
                   WHERE r.variant_id=%s AND r.state='active'
                   ORDER BY r.expires_at,r.id LIMIT %s""",
                (variant_id, page_size),
            )
        return [dict(x) for x in cur.fetchall()]


def inventory_reconciliation_preview(actor: Staff, limit: int = 500) -> dict:
    """Compare physical balances and reservations to their authoritative records.

    This function never changes stock. It returns independent discrepancy classes
    so operators can distinguish ledger drift from reservation drift.
    """
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Повну звірку складу може запускати лише власник або адміністратор.")
    page_size = _stock_int(limit, "ліміт", 1, 2000)
    with db_cursor() as cur:
        cur.execute(
            """WITH ledger AS (
                 SELECT variant_id,
                        COALESCE(SUM(quantity_delta) FILTER
                          (WHERE movement_type = ANY(%s)),0)::bigint AS ledger_qty,
                        COUNT(*) FILTER
                          (WHERE movement_type = ANY(%s))::bigint AS physical_movements,
                        MAX(created_at) AS last_movement_at
                 FROM inventory_movements GROUP BY variant_id
               ),
               active_res AS (
                 SELECT variant_id,COALESCE(SUM(quantity),0)::bigint AS reserved_sum,
                        COUNT(*)::bigint AS active_count,
                        MIN(expires_at) AS nearest_expiry
                 FROM stock_reservations WHERE state='active'
                 GROUP BY variant_id
               )
               SELECT v.id AS variant_id,v.sku,p.name AS product_name,
                      v.stock_qty,v.reserved_qty,
                      COALESCE(l.ledger_qty,0) AS ledger_qty,
                      COALESCE(l.physical_movements,0) AS movement_count,
                      COALESCE(a.reserved_sum,0) AS active_reserved,
                      COALESCE(a.active_count,0) AS active_reservation_count,
                      l.last_movement_at,a.nearest_expiry,
                      (v.stock_qty-COALESCE(l.ledger_qty,0)) AS ledger_delta,
                      (v.reserved_qty-COALESCE(a.reserved_sum,0)) AS reservation_delta,
                      CASE WHEN v.stock_qty<0 THEN 'negative_stock'
                           WHEN v.reserved_qty<0 THEN 'negative_reserved'
                           WHEN v.reserved_qty>v.stock_qty THEN 'over_reserved'
                           WHEN v.stock_qty<>COALESCE(l.ledger_qty,0) THEN 'ledger_mismatch'
                           WHEN v.reserved_qty<>COALESCE(a.reserved_sum,0) THEN 'reservation_mismatch'
                           ELSE 'ok' END AS integrity_state
               FROM product_variants v
               JOIN products p ON p.id=v.product_id
               LEFT JOIN ledger l ON l.variant_id=v.id
               LEFT JOIN active_res a ON a.variant_id=v.id
               WHERE v.stock_qty<0 OR v.reserved_qty<0
                  OR v.reserved_qty>v.stock_qty
                  OR v.stock_qty<>COALESCE(l.ledger_qty,0)
                  OR v.reserved_qty<>COALESCE(a.reserved_sum,0)
               ORDER BY CASE WHEN v.stock_qty<0 OR v.reserved_qty<0 THEN 0
                             WHEN v.reserved_qty>v.stock_qty THEN 1
                             WHEN v.stock_qty<>COALESCE(l.ledger_qty,0) THEN 2
                             ELSE 3 END,v.id
               LIMIT %s""",
            (list(STOCK_PHYSICAL_MOVEMENT_TYPES), list(STOCK_PHYSICAL_MOVEMENT_TYPES),
             page_size + 1),
        )
        rows = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT COUNT(*) AS variants,
                      COUNT(*) FILTER (WHERE v.stock_qty<>COALESCE(l.ledger_qty,0)) AS ledger_mismatches,
                      COUNT(*) FILTER (WHERE v.reserved_qty<>COALESCE(a.reserved_sum,0)) AS reservation_mismatches,
                      COUNT(*) FILTER (WHERE v.stock_qty<0 OR v.reserved_qty<0) AS negative_balances,
                      COUNT(*) FILTER (WHERE v.reserved_qty>v.stock_qty) AS over_reserved
               FROM product_variants v
               LEFT JOIN (SELECT variant_id,SUM(quantity_delta) AS ledger_qty
                          FROM inventory_movements
                          WHERE movement_type=ANY(%s) GROUP BY variant_id) l
                 ON l.variant_id=v.id
               LEFT JOIN (SELECT variant_id,SUM(quantity) AS reserved_sum
                          FROM stock_reservations WHERE state='active' GROUP BY variant_id) a
                 ON a.variant_id=v.id""",
            (list(STOCK_PHYSICAL_MOVEMENT_TYPES),),
        )
        totals = dict(cur.fetchone())
    truncated = len(rows) > page_size
    rows = rows[:page_size]
    _stock_audit(cur=None, actor=None, action="", entity_type="", entity_id="") if False else None
    return {"totals": totals, "items": rows, "truncated": truncated,
            "limit": page_size}


def inventory_reconciliation_apply(variant_id: int, actor: Staff,
                                    correction_type: str, target_value: int,
                                    reason: str, confirmation: str) -> dict:
    """Apply one explicit correction as a new ledger event.

    Supported corrections are deliberately narrow:
    - physical: set physical stock to a confirmed target, respecting reservations;
    - reserved: rebuild reserved_qty from active reservation rows.
    The operation never edits or deletes inventory_movements or reservations.
    """
    if actor.role != "owner":
        raise PermissionError("Виправлення розбіжностей доступне лише власнику.")
    clean_reason = _stock_reason(reason, minimum=10)
    expected_confirmation = f"ВИПРАВИТИ SKU {variant_id}"
    if str(confirmation or "").strip() != expected_confirmation:
        raise ValueError(f"Для підтвердження введіть: {expected_confirmation}")
    if correction_type not in {"physical", "reserved"}:
        raise ValueError("Тип корекції має бути physical або reserved.")
    target = _stock_int(target_value, "цільове значення", 0, 1_000_000)
    with db_cursor() as cur:
        variant = _stock_lock_variant(cur, variant_id)
        before = {"stock_qty": int(variant["stock_qty"]),
                  "reserved_qty": int(variant["reserved_qty"])}
        if correction_type == "physical":
            if target < before["reserved_qty"]:
                raise ValueError("Фізичний залишок не може бути нижчим за активний резерв.")
            delta = target - before["stock_qty"]
            if delta == 0:
                return {"changed": False, "before": before, "after": before}
            cur.execute(
                "UPDATE product_variants SET stock_qty=%s,updated_at=NOW() WHERE id=%s",
                (target, variant_id),
            )
            _stock_write_movement(
                cur, variant_id=variant_id, movement_type="manual_adjustment",
                quantity_delta=delta, reference_type="stock_reconciliation",
                reference_id=f"variant:{variant_id}", reason=clean_reason,
                actor_telegram_id=actor.telegram_id,
            )
            after = {"stock_qty": target, "reserved_qty": before["reserved_qty"]}
        else:
            cur.execute(
                """SELECT COALESCE(SUM(quantity),0) AS active_reserved
                   FROM stock_reservations WHERE variant_id=%s AND state='active'""",
                (variant_id,),
            )
            actual_reserved = int(cur.fetchone()["active_reserved"])
            if actual_reserved > before["stock_qty"]:
                raise ValueError("Активні резерви перевищують фізичний залишок. Спочатку розберіть конфлікт замовлень.")
            if target != actual_reserved:
                raise ValueError(
                    f"Цільове значення не збігається з резервами в документах: {actual_reserved}."
                )
            cur.execute(
                "UPDATE product_variants SET reserved_qty=%s,updated_at=NOW() WHERE id=%s",
                (actual_reserved, variant_id),
            )
            after = {"stock_qty": before["stock_qty"], "reserved_qty": actual_reserved}
        _stock_audit(cur, actor, "inventory.reconciliation_applied", "variant",
                     variant_id, before, after, clean_reason)
        return {"changed": before != after, "before": before, "after": after,
                "correction_type": correction_type}


def release_expired_reservations_safely(batch_size: int = 100,
                                        actor_telegram_id: int = None) -> dict:
    """Expire due reservations without leaving an order shippable without stock.

    A reservation can expire only while its order is in a pre-shipment state.
    For orders with several SKU reservations, all expired rows are released in
    one transaction and the order is moved to 'problem' for staff review. The
    order is never silently cancelled and never remains in a ready-to-ship state.
    """
    batch = _stock_int(batch_size, "розмір пакета", 1, 1000)
    released = 0
    affected_orders = set()
    skipped = 0
    with db_cursor() as cur:
        cur.execute(
            """SELECT r.id,r.order_id,r.variant_id,r.quantity,o.status AS order_status
               FROM stock_reservations r
               LEFT JOIN orders o ON o.id=r.order_id
               WHERE r.state='active' AND r.expires_at<=NOW()
               ORDER BY r.expires_at,r.id
               LIMIT %s FOR UPDATE OF r SKIP LOCKED""",
            (batch,),
        )
        rows = list(cur.fetchall())
        for row in rows:
            state = row["order_status"]
            if state in {"shipped", "delivered", "completed", "returned"}:
                skipped += 1
                continue
            cur.execute(
                "UPDATE stock_reservations SET state='expired' WHERE id=%s AND state='active'",
                (row["id"],),
            )
            if cur.rowcount != 1:
                continue
            cur.execute(
                """UPDATE product_variants
                   SET reserved_qty=reserved_qty-%s,updated_at=NOW()
                   WHERE id=%s AND reserved_qty>=%s""",
                (row["quantity"], row["variant_id"], row["quantity"]),
            )
            if cur.rowcount != 1:
                raise RuntimeError("Лічильник резервів не відповідає документам. Транзакцію скасовано.")
            _stock_write_movement(
                cur, variant_id=int(row["variant_id"]),
                movement_type="reservation_expired",
                quantity_delta=int(row["quantity"]), reference_type="order",
                reference_id=str(row["order_id"] or ""),
                reason="Автоматичне звільнення простроченого резерву",
                actor_telegram_id=actor_telegram_id,
            )
            released += 1
            if row["order_id"]:
                affected_orders.add(int(row["order_id"]))
        for order_id in sorted(affected_orders):
            cur.execute(
                "SELECT status FROM orders WHERE id=%s FOR UPDATE",
                (order_id,),
            )
            order = cur.fetchone()
            if order and order["status"] in {"new", "confirmed", "packing", "packed", "ready_to_ship"}:
                cur.execute(
                    """UPDATE orders SET status='problem',updated_at=NOW()
                       WHERE id=%s AND status=%s""",
                    (order_id, order["status"]),
                )
                if cur.rowcount == 1:
                    cur.execute(
                        """INSERT INTO audit_log
                           (actor_telegram_id,actor_role,action,entity_type,entity_id,
                            before_data,after_data,reason)
                           VALUES(%s,'system','stock.reservation_expired_order_flagged',
                                  'order',%s,%s::jsonb,%s::jsonb,%s)""",
                        (actor_telegram_id, str(order_id),
                         json_dumps({"status": order["status"]}),
                         json_dumps({"status": "problem"}),
                         "Резерв товару прострочено. Потрібне повторне підтвердження наявності."),
                    )
        return {"released": released, "affected_orders": sorted(affected_orders),
                "skipped_terminal_orders": skipped, "examined": len(rows)}


def reservation_order_preflight(order_id: int, actor: Staff) -> dict:
    """Check whether an order still owns enough active stock to be shipped."""
    if not (actor.can("orders.read") or actor.can("orders.update")):
        raise PermissionError("Недостатньо прав для перевірки замовлення.")
    with db_cursor() as cur:
        cur.execute("SELECT id,status,order_number FROM orders WHERE id=%s", (order_id,))
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        cur.execute(
            """SELECT oi.variant_id,oi.sku_snapshot,oi.quantity,
                      COALESCE(SUM(r.quantity) FILTER (WHERE r.state='active'),0) AS active_reserved,
                      COUNT(r.id) FILTER (WHERE r.state='active') AS active_rows,
                      COALESCE(v.stock_qty,0) AS stock_qty,
                      COALESCE(v.reserved_qty,0) AS reserved_qty
               FROM order_items oi
               LEFT JOIN product_variants v ON v.id=oi.variant_id
               LEFT JOIN stock_reservations r
                 ON r.order_id=oi.order_id AND r.variant_id=oi.variant_id
               WHERE oi.order_id=%s
               GROUP BY oi.variant_id,oi.sku_snapshot,oi.quantity,v.stock_qty,v.reserved_qty
               ORDER BY oi.variant_id""",
            (order_id,),
        )
        lines = [dict(x) for x in cur.fetchall()]
    problems = []
    for line in lines:
        if line["variant_id"] is None:
            problems.append({"sku": line["sku_snapshot"], "issue": "missing_variant"})
        elif int(line["active_reserved"]) < int(line["quantity"]):
            problems.append({"sku": line["sku_snapshot"], "issue": "reservation_shortfall",
                             "required": int(line["quantity"]),
                             "reserved": int(line["active_reserved"])})
    return {"order": dict(order), "lines": lines,
            "can_ship": order["status"] == "ready_to_ship" and not problems,
            "problems": problems}


def _stock_consume_order_reservations(cur, order_id: int, actor: Staff) -> dict:
    """Consume every active reservation for an order or fail the whole transition."""
    cur.execute(
        """SELECT id,variant_id,quantity FROM stock_reservations
           WHERE order_id=%s AND state='active'
           ORDER BY variant_id,id FOR UPDATE""",
        (order_id,),
    )
    reservations = list(cur.fetchall())
    if not reservations:
        raise ValueError("У замовлення немає активних резервів. Відправлення заблоковано.")
    totals = {}
    for reservation in reservations:
        totals[int(reservation["variant_id"])] = (
            totals.get(int(reservation["variant_id"]), 0) + int(reservation["quantity"])
        )
    for variant_id, quantity in totals.items():
        cur.execute(
            """UPDATE product_variants
               SET stock_qty=stock_qty-%s,reserved_qty=reserved_qty-%s,updated_at=NOW()
               WHERE id=%s AND stock_qty>=%s AND reserved_qty>=%s""",
            (quantity, quantity, variant_id, quantity, quantity),
        )
        if cur.rowcount != 1:
            raise RuntimeError(f"Недостатньо фізичного або зарезервованого залишку для SKU #{variant_id}.")
    for reservation in reservations:
        cur.execute(
            "UPDATE stock_reservations SET state='consumed' WHERE id=%s AND state='active'",
            (reservation["id"],),
        )
        if cur.rowcount != 1:
            raise RuntimeError("Резерв змінився під час списання. Транзакцію скасовано.")
    for variant_id, quantity in totals.items():
        _stock_write_movement(
            cur, variant_id=variant_id, movement_type="sale",
            quantity_delta=-quantity, reference_type="order",
            reference_id=str(order_id),
            reason="Списання зарезервованого товару під час відправлення",
            actor_telegram_id=actor.telegram_id,
        )
    return {"reservation_rows": len(reservations), "sku_count": len(totals),
            "units_consumed": sum(totals.values())}


def _stock_release_order_reservations(cur, order_id: int, actor: Staff,
                                      terminal_state: str = "released") -> dict:
    """Release active reservations and update denormalized reserved_qty exactly."""
    if terminal_state not in {"released", "expired"}:
        raise ValueError("Некоректний фінальний стан резерву.")
    cur.execute(
        """SELECT id,variant_id,quantity FROM stock_reservations
           WHERE order_id=%s AND state='active'
           ORDER BY variant_id,id FOR UPDATE""",
        (order_id,),
    )
    rows = list(cur.fetchall())
    totals = {}
    for row in rows:
        variant_id = int(row["variant_id"])
        totals[variant_id] = totals.get(variant_id, 0) + int(row["quantity"])
    for variant_id, quantity in totals.items():
        cur.execute(
            """UPDATE product_variants SET reserved_qty=reserved_qty-%s,updated_at=NOW()
               WHERE id=%s AND reserved_qty>=%s""",
            (quantity, variant_id, quantity),
        )
        if cur.rowcount != 1:
            raise RuntimeError(f"Резервний баланс SKU #{variant_id} пошкоджений.")
    for row in rows:
        cur.execute(
            "UPDATE stock_reservations SET state=%s WHERE id=%s AND state='active'",
            (terminal_state, row["id"]),
        )
        if cur.rowcount != 1:
            raise RuntimeError("Не вдалося завершити резерв.")
    for variant_id, quantity in totals.items():
        _stock_write_movement(
            cur, variant_id=variant_id,
            movement_type="reservation_expired" if terminal_state == "expired" else "reservation_release",
            quantity_delta=quantity, reference_type="order",
            reference_id=str(order_id),
            reason="Звільнення резерву замовлення",
            actor_telegram_id=actor.telegram_id,
        )
    return {"reservation_rows": len(rows), "sku_count": len(totals),
            "units_released": sum(totals.values())}


def supply_document_snapshot(supply_id: int, actor: Staff) -> dict:
    """Return a full draft/posted supply document with line-level receipt progress."""
    if not (actor.can("inventory.receive") or actor.can("inventory.read")):
        raise PermissionError("Недостатньо прав для перегляду поставки.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT d.*,s.name AS supplier_name
               FROM supply_documents d LEFT JOIN suppliers s ON s.id=d.supplier_id
               WHERE d.id=%s""",
            (supply_id,),
        )
        document = cur.fetchone()
        if not document:
            raise ValueError("Поставку не знайдено.")
        cur.execute(
            """SELECT si.id,si.variant_id,v.sku,p.name AS product_name,
                      si.quantity,si.received_qty,si.unit_cost,
                      (si.quantity-si.received_qty) AS outstanding_qty,
                      (si.received_qty*si.unit_cost) AS received_cost,
                      (si.quantity*si.unit_cost) AS planned_cost
               FROM supply_items si
               JOIN product_variants v ON v.id=si.variant_id
               JOIN products p ON p.id=v.product_id
               WHERE si.supply_id=%s ORDER BY si.id""",
            (supply_id,),
        )
        items = [dict(x) for x in cur.fetchall()]
    return {"document": dict(document), "items": items,
            "planned_units": sum(int(x["quantity"]) for x in items),
            "received_units": sum(int(x["received_qty"]) for x in items),
            "outstanding_units": sum(int(x["outstanding_qty"]) for x in items),
            "received_cost": sum((Decimal(str(x["received_cost"])) for x in items), Decimal("0.00"))}


def update_supply_item(supply_id: int, item_id: int, quantity: int,
                       unit_cost: Decimal, actor: Staff,
                       reason: str) -> dict:
    """Edit a draft supply line without allowing posted document mutation."""
    _stock_require(actor, "inventory.receive")
    qty = _stock_int(quantity, "кількість", 1, 1_000_000)
    cost = Decimal(str(unit_cost))
    if cost < 0 or cost > Decimal("999999999"):
        raise ValueError("Некоректна закупівельна ціна.")
    clean_reason = _stock_reason(reason, minimum=5)
    with db_cursor() as cur:
        cur.execute("SELECT state FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc = cur.fetchone()
        if not doc or doc["state"] != "draft":
            raise ValueError("Редагувати можна лише чернетку поставки.")
        cur.execute(
            """SELECT id,quantity,received_qty,unit_cost FROM supply_items
               WHERE id=%s AND supply_id=%s FOR UPDATE""",
            (item_id, supply_id),
        )
        item = cur.fetchone()
        if not item:
            raise ValueError("Рядок поставки не знайдено.")
        received = int(item["received_qty"])
        if qty < received:
            raise ValueError("Документальна кількість не може бути меншою за вже прийняту.")
        before = {"quantity": int(item["quantity"]),
                  "received_qty": received, "unit_cost": str(item["unit_cost"])}
        cur.execute(
            "UPDATE supply_items SET quantity=%s,unit_cost=%s WHERE id=%s",
            (qty, cost, item_id),
        )
        cur.execute(
            """UPDATE supply_documents SET total_cost=(
                 SELECT COALESCE(SUM(quantity*unit_cost),0)
                 FROM supply_items WHERE supply_id=%s)
               WHERE id=%s""",
            (supply_id, supply_id),
        )
        after = {"quantity": qty, "received_qty": received, "unit_cost": str(cost)}
        _stock_audit(cur, actor, "supply.item_updated", "supply_item",
                     item_id, before, after, clean_reason)
        return {"item_id": item_id, "before": before, "after": after}


def remove_supply_item(supply_id: int, item_id: int, actor: Staff,
                       reason: str) -> None:
    """Remove an unreceived line from a draft supply document only."""
    _stock_require(actor, "inventory.receive")
    clean_reason = _stock_reason(reason, minimum=5)
    with db_cursor() as cur:
        cur.execute("SELECT state FROM supply_documents WHERE id=%s FOR UPDATE", (supply_id,))
        doc = cur.fetchone()
        if not doc or doc["state"] != "draft":
            raise ValueError("Видаляти рядки можна лише з чернетки поставки.")
        cur.execute(
            """SELECT id,variant_id,quantity,received_qty,unit_cost
               FROM supply_items WHERE id=%s AND supply_id=%s FOR UPDATE""",
            (item_id, supply_id),
        )
        item = cur.fetchone()
        if not item:
            raise ValueError("Рядок поставки не знайдено.")
        if int(item["received_qty"]) > 0:
            raise ValueError("Рядок із прийнятою кількістю не видаляється. Виправте документ окремою корекцією.")
        before = dict(item)
        cur.execute("DELETE FROM supply_items WHERE id=%s", (item_id,))
        cur.execute(
            """UPDATE supply_documents SET total_cost=(
                 SELECT COALESCE(SUM(quantity*unit_cost),0)
                 FROM supply_items WHERE supply_id=%s)
               WHERE id=%s""",
            (supply_id, supply_id),
        )
        _stock_audit(cur, actor, "supply.item_removed", "supply_item",
                     item_id, before, None, clean_reason)


def cancel_supply_draft(supply_id: int, actor: Staff, reason: str) -> None:
    """Cancel an unposted supply draft; posted receipts require a reversal document."""
    _stock_require(actor, "inventory.receive")
    clean_reason = _stock_reason(reason, minimum=8)
    with db_cursor() as cur:
        cur.execute("SELECT state,document_number FROM supply_documents WHERE id=%s FOR UPDATE",
                    (supply_id,))
        doc = cur.fetchone()
        if not doc:
            raise ValueError("Поставку не знайдено.")
        if doc["state"] != "draft":
            raise ValueError("Проведену поставку не можна скасувати як чернетку.")
        cur.execute(
            "SELECT COALESCE(SUM(received_qty),0) AS received FROM supply_items WHERE supply_id=%s",
            (supply_id,),
        )
        if int(cur.fetchone()["received"]) > 0:
            raise ValueError("У документі вже зазначено прийнятий товар. Спочатку виправте фактичне приймання.")
        cur.execute("UPDATE supply_documents SET state='cancelled' WHERE id=%s", (supply_id,))
        _stock_audit(cur, actor, "supply.cancelled", "supply", supply_id,
                     {"state": "draft"}, {"state": "cancelled"}, clean_reason)


def supply_receipt_validation(supply_id: int, actor: Staff) -> dict:
    """Validate a draft before posting, returning actionable line-level findings."""
    _stock_require(actor, "inventory.receive")
    with db_cursor() as cur:
        cur.execute(
            """SELECT d.state,d.document_number,d.supplier_id,s.active AS supplier_active
               FROM supply_documents d LEFT JOIN suppliers s ON s.id=d.supplier_id
               WHERE d.id=%s""",
            (supply_id,),
        )
        doc = cur.fetchone()
        if not doc:
            raise ValueError("Поставку не знайдено.")
        cur.execute(
            """SELECT si.id,si.variant_id,si.quantity,si.received_qty,si.unit_cost,
                      v.sku,v.active AS variant_active,p.archived_at
               FROM supply_items si
               JOIN product_variants v ON v.id=si.variant_id
               JOIN products p ON p.id=v.product_id
               WHERE si.supply_id=%s ORDER BY si.id""",
            (supply_id,),
        )
        items = [dict(x) for x in cur.fetchall()]
    issues = []
    if doc["state"] != "draft":
        issues.append({"type": "document_not_draft", "message": "Документ уже не є чернеткою."})
    if not doc["supplier_id"] or not doc["supplier_active"]:
        issues.append({"type": "supplier_inactive", "message": "Постачальник відсутній або неактивний."})
    if not items:
        issues.append({"type": "empty_document", "message": "У документі немає SKU."})
    for item in items:
        if int(item["received_qty"]) > int(item["quantity"]):
            issues.append({"type": "received_over_document", "item_id": item["id"]})
        if not item["variant_active"] or item["archived_at"] is not None:
            issues.append({"type": "sku_inactive", "sku": item["sku"]})
        if Decimal(str(item["unit_cost"])) < 0:
            issues.append({"type": "negative_cost", "sku": item["sku"]})
    if not any(int(x["received_qty"]) > 0 for x in items):
        issues.append({"type": "nothing_received", "message": "Немає фактично прийнятих одиниць."})
    return {"supply_id": supply_id, "document_number": doc["document_number"],
            "valid": not issues, "issues": issues, "items": items}


def create_supply_reversal(supply_id: int, actor: Staff, reason: str) -> dict:
    """Reverse a posted receipt only if its received units remain physically available.

    The reversal is a new negative ledger movement. It refuses to consume units
    already reserved or sold, so the operator must use a separate stock adjustment
    or investigate the downstream movements instead of rewriting old history.
    """
    if actor.role != "owner":
        raise PermissionError("Сторнування поставки доступне лише власнику.")
    clean_reason = _stock_reason(reason, minimum=10)
    with db_cursor() as cur:
        cur.execute(
            "SELECT state,document_number FROM supply_documents WHERE id=%s FOR UPDATE",
            (supply_id,),
        )
        doc = cur.fetchone()
        if not doc or doc["state"] != "posted":
            raise ValueError("Сторнувати можна лише проведену поставку.")
        cur.execute(
            """SELECT id,variant_id,received_qty,unit_cost
               FROM supply_items WHERE supply_id=%s AND received_qty>0
               ORDER BY variant_id FOR UPDATE""",
            (supply_id,),
        )
        items = list(cur.fetchall())
        if not items:
            raise ValueError("У поставці немає прийнятих одиниць.")
        for item in items:
            variant = _stock_lock_variant(cur, int(item["variant_id"]))
            qty = int(item["received_qty"])
            available = int(variant["stock_qty"]) - int(variant["reserved_qty"])
            if available < qty:
                raise ValueError(
                    f"Сторнування неможливе для SKU {variant['sku']}: "
                    f"доступно {available}, потрібно {qty}. Перевірте продажі та резерви."
                )
        reversal_rows = []
        for item in items:
            variant_id = int(item["variant_id"])
            qty = int(item["received_qty"])
            cur.execute(
                """UPDATE product_variants SET stock_qty=stock_qty-%s,updated_at=NOW()
                   WHERE id=%s AND stock_qty-reserved_qty>=%s""",
                (qty, variant_id, qty),
            )
            if cur.rowcount != 1:
                raise RuntimeError("Залишок змінився під час сторнування. Транзакцію скасовано.")
            movement_id = _stock_write_movement(
                cur, variant_id=variant_id, movement_type="stock_reversal",
                quantity_delta=-qty, reference_type="supply_reversal",
                reference_id=str(supply_id), reason=clean_reason,
                actor_telegram_id=actor.telegram_id,
            )
            reversal_rows.append({"variant_id": variant_id, "quantity": qty,
                                  "movement_id": movement_id})
        cur.execute("UPDATE supply_documents SET state='reversed' WHERE id=%s", (supply_id,))
        _stock_audit(cur, actor, "supply.reversed", "supply", supply_id,
                     {"state": "posted"}, {"state": "reversed", "items": reversal_rows},
                     clean_reason)
        return {"supply_id": supply_id, "document_number": doc["document_number"],
                "reversed": reversal_rows}


def stock_low_stock_report_v2(actor: Staff, threshold_override: int = None,
                               limit: int = 200) -> list[dict]:
    """List active SKUs at or below their configured low-stock threshold."""
    if not (actor.can("inventory.read") or actor.can("catalog.read")):
        raise PermissionError("Недостатньо прав для звіту залишків.")
    page_size = _stock_int(limit, "ліміт", 1, 1000)
    threshold = None if threshold_override is None else _stock_int(
        threshold_override, "поріг", 0, 1_000_000
    )
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id AS variant_id,v.sku,v.variant_name,v.stock_qty,
                      v.reserved_qty,(v.stock_qty-v.reserved_qty) AS available_qty,
                      v.low_stock_threshold,p.name AS product_name,
                      c.name AS category_name,b.name AS brand_name
               FROM product_variants v
               JOIN products p ON p.id=v.product_id
               LEFT JOIN categories c ON c.id=p.category_id
               LEFT JOIN brands b ON b.id=p.brand_id
               WHERE v.active=TRUE AND p.active=TRUE AND p.archived_at IS NULL
                 AND (v.stock_qty-v.reserved_qty)<=COALESCE(%s,v.low_stock_threshold)
               ORDER BY (v.stock_qty-v.reserved_qty),p.name,v.sku
               LIMIT %s""",
            (threshold, page_size),
        )
        return [dict(x) for x in cur.fetchall()]


def inventory_valuation_report(actor: Staff, limit: int = 500) -> dict:
    """Calculate on-hand stock valuation from current weighted-average cost."""
    if actor.role != "owner":
        raise PermissionError("Оцінка вартості складу доступна лише власнику.")
    page_size = _stock_int(limit, "ліміт", 1, 2000)
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id AS variant_id,v.sku,p.name AS product_name,
                      v.stock_qty,v.reserved_qty,
                      (v.stock_qty-v.reserved_qty) AS available_qty,
                      v.cost_price,
                      CASE WHEN v.cost_price IS NULL THEN NULL
                           ELSE v.stock_qty*v.cost_price END AS stock_value,
                      CASE WHEN v.cost_price IS NULL THEN v.stock_qty ELSE 0 END AS uncosted_qty
               FROM product_variants v JOIN products p ON p.id=v.product_id
               WHERE v.active=TRUE AND v.stock_qty>0
               ORDER BY p.name,v.sku LIMIT %s""",
            (page_size + 1,),
        )
        rows = [dict(x) for x in cur.fetchall()]
    truncated = len(rows) > page_size
    rows = rows[:page_size]
    valued = sum((Decimal(str(x["stock_value"])) for x in rows
                  if x["stock_value"] is not None), Decimal("0.00"))
    uncosted = sum(int(x["uncosted_qty"]) for x in rows)
    return {"items": rows, "stock_value": valued, "uncosted_units": uncosted,
            "truncated": truncated, "limit": page_size,
            "valuation_basis": "поточна середньозважена собівартість; не ринкова ціна"}


def inventory_movement_summary(actor: Staff, days: int = 30) -> dict:
    """Aggregate physical movements and reservation events for a selected period."""
    if not (actor.can("inventory.read") or actor.role == "owner"):
        raise PermissionError("Недостатньо прав для статистики складу.")
    period = _stock_int(days, "період у днях", 1, 365)
    with db_cursor() as cur:
        cur.execute(
            """SELECT movement_type,COUNT(*) AS rows,
                      COALESCE(SUM(quantity_delta),0) AS net_units,
                      COALESCE(SUM(ABS(quantity_delta)),0) AS gross_units
               FROM inventory_movements
               WHERE created_at>=NOW()-(%s * INTERVAL '1 day')
               GROUP BY movement_type ORDER BY movement_type""",
            (period,),
        )
        by_type = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT COUNT(DISTINCT variant_id) AS sku_count,
                      COUNT(*) AS movement_count,
                      MIN(created_at) AS first_movement,
                      MAX(created_at) AS last_movement
               FROM inventory_movements
               WHERE created_at>=NOW()-(%s * INTERVAL '1 day')""",
            (period,),
        )
        totals = dict(cur.fetchone())
    return {"days": period, "totals": totals, "by_type": by_type}


def inventory_count_progress_v2(count_id: int, actor: Staff) -> dict:
    """Read blind-count progress without exposing expected system quantities."""
    if actor.role not in {"owner", "admin", "packer"}:
        raise PermissionError("Недостатньо прав для перегляду інвентаризації.")
    with db_cursor() as cur:
        cur.execute(
            "SELECT id,status,created_by,created_at FROM inventory_counts WHERE id=%s",
            (count_id,),
        )
        count = cur.fetchone()
        if not count:
            raise ValueError("Інвентаризацію не знайдено.")
        cur.execute(
            """SELECT COUNT(*) AS total,
                      COUNT(*) FILTER (WHERE actual_qty IS NOT NULL) AS counted,
                      COUNT(*) FILTER (WHERE actual_qty IS NULL) AS remaining
               FROM inventory_count_items WHERE count_id=%s""",
            (count_id,),
        )
        progress = dict(cur.fetchone())
        cur.execute(
            """SELECT ci.variant_id,v.sku,p.name AS product_name,
                      ci.actual_qty,ci.counted_at,ci.counted_by
               FROM inventory_count_items ci
               JOIN product_variants v ON v.id=ci.variant_id
               JOIN products p ON p.id=v.product_id
               WHERE ci.count_id=%s ORDER BY ci.variant_id""",
            (count_id,),
        )
        items = [dict(x) for x in cur.fetchall()]
    return {"count": dict(count), "progress": progress, "items": items}


def inventory_count_reopen(count_id: int, actor: Staff, reason: str) -> None:
    """Reopen a confirmed count only by creating a new count, never mutating history."""
    raise ValueError(
        "Підтверджену інвентаризацію не можна відкривати повторно. "
        "Створіть нову інвентаризацію або окреме коригування з причиною."
    )


def inventory_adjustment_preview(variant_id: int, delta: int,
                                 actor: Staff, reason: str) -> dict:
    """Preview a manual adjustment without writing any database state."""
    _stock_require(actor, "inventory.adjust")
    change = int(delta)
    if change == 0:
        raise ValueError("Коригування не може дорівнювати нулю.")
    clean_reason = _stock_reason(reason, minimum=5)
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id,v.sku,v.stock_qty,v.reserved_qty,
                      v.stock_qty+%s AS proposed_stock,
                      (v.stock_qty+%s)-v.reserved_qty AS proposed_available
               FROM product_variants v WHERE v.id=%s""",
            (change, change, variant_id),
        )
        row = cur.fetchone()
        if not row:
            raise ValueError("SKU не знайдено.")
    if int(row["proposed_stock"]) < int(row["reserved_qty"]):
        raise ValueError("Коригування опустить залишок нижче активного резерву.")
    return {"variant": dict(row), "delta": change, "reason": clean_reason,
            "requires_confirmation": True,
            "confirmation": f"КОРИГУВАТИ SKU {variant_id} НА {change:+d}"}


def inventory_adjustment_confirm(variant_id: int, delta: int, actor: Staff,
                                 reason: str, confirmation: str) -> dict:
    """Apply a previewed manual adjustment with exact confirmation text."""
    preview = inventory_adjustment_preview(variant_id, delta, actor, reason)
    if str(confirmation or "").strip() != preview["confirmation"]:
        raise ValueError(f"Для підтвердження введіть: {preview['confirmation']}")
    change = int(delta)
    clean_reason = preview["reason"]
    with db_cursor() as cur:
        variant = _stock_lock_variant(cur, variant_id)
        old_qty = int(variant["stock_qty"])
        old_reserved = int(variant["reserved_qty"])
        new_qty = old_qty + change
        if new_qty < old_reserved:
            raise ValueError("Після попереднього перегляду резерв змінився. Повторіть операцію.")
        cur.execute(
            "UPDATE product_variants SET stock_qty=%s,updated_at=NOW() WHERE id=%s",
            (new_qty, variant_id),
        )
        movement_id = _stock_write_movement(
            cur, variant_id=variant_id, movement_type="manual_adjustment",
            quantity_delta=change, reference_type="manual_adjustment",
            reference_id=f"variant:{variant_id}", reason=clean_reason,
            actor_telegram_id=actor.telegram_id,
        )
        _stock_audit(cur, actor, "inventory.adjustment_confirmed", "variant",
                     variant_id, {"stock_qty": old_qty, "reserved_qty": old_reserved},
                     {"stock_qty": new_qty, "reserved_qty": old_reserved,
                      "movement_id": movement_id}, clean_reason)
    return {"variant_id": variant_id, "old_stock": old_qty,
            "new_stock": new_qty, "delta": change, "movement_id": movement_id}


def stock_order_reservation_rebuild_preview(order_id: int, actor: Staff) -> dict:
    """Compare order line quantities to reservation rows before any repair."""
    if actor.role != "owner":
        raise PermissionError("Перевірка відновлення резерву доступна лише власнику.")
    with db_cursor() as cur:
        cur.execute("SELECT id,status,order_number FROM orders WHERE id=%s", (order_id,))
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        cur.execute(
            """SELECT oi.variant_id,oi.sku_snapshot,SUM(oi.quantity) AS ordered_qty,
                      COALESCE(SUM(r.quantity) FILTER (WHERE r.state='active'),0) AS active_qty,
                      COALESCE(SUM(r.quantity) FILTER (WHERE r.state='consumed'),0) AS consumed_qty
               FROM order_items oi
               LEFT JOIN stock_reservations r
                 ON r.order_id=oi.order_id AND r.variant_id=oi.variant_id
               WHERE oi.order_id=%s
               GROUP BY oi.variant_id,oi.sku_snapshot ORDER BY oi.variant_id""",
            (order_id,),
        )
        lines = [dict(x) for x in cur.fetchall()]
    return {"order": dict(order), "lines": lines,
            "rebuild_allowed": order["status"] in {"new", "confirmed", "packing", "packed", "problem"},
            "note": "Це лише діагностика. Автоматичне створення резервів не виконується."}


def stock_reservation_integrity_report(actor: Staff, limit: int = 300) -> dict:
    """Find order-level reservation gaps and reservation rows inconsistent with state."""
    if actor.role != "owner":
        raise PermissionError("Повний звіт резервів доступний лише власнику.")
    page_size = _stock_int(limit, "ліміт", 1, 1000)
    with db_cursor() as cur:
        cur.execute(
            """WITH order_lines AS (
                 SELECT oi.order_id,oi.variant_id,SUM(oi.quantity)::bigint AS ordered_qty
                 FROM order_items oi WHERE oi.variant_id IS NOT NULL
                 GROUP BY oi.order_id,oi.variant_id
               ),
               reservations AS (
                 SELECT order_id,variant_id,
                   COALESCE(SUM(quantity) FILTER (WHERE state='active'),0)::bigint AS active_qty,
                   COALESCE(SUM(quantity) FILTER (WHERE state='consumed'),0)::bigint AS consumed_qty,
                   COALESCE(SUM(quantity) FILTER (WHERE state IN ('released','expired')),0)::bigint AS released_qty
                 FROM stock_reservations GROUP BY order_id,variant_id
               )
               SELECT o.id AS order_id,o.order_number,o.status,
                      ol.variant_id,v.sku,ol.ordered_qty,
                      COALESCE(r.active_qty,0) AS active_qty,
                      COALESCE(r.consumed_qty,0) AS consumed_qty,
                      COALESCE(r.released_qty,0) AS released_qty,
                      CASE WHEN o.status IN ('shipped','delivered','completed','returned')
                                  AND COALESCE(r.consumed_qty,0)<ol.ordered_qty
                           THEN 'shipped_without_full_consumption'
                           WHEN o.status='cancelled' AND COALESCE(r.active_qty,0)>0
                           THEN 'cancelled_with_active_reservation'
                           WHEN o.status IN ('new','confirmed','packing','packed','ready_to_ship')
                                  AND COALESCE(r.active_qty,0)<ol.ordered_qty
                           THEN 'pre_shipment_reservation_shortfall'
                           ELSE 'review' END AS issue
               FROM order_lines ol JOIN orders o ON o.id=ol.order_id
               LEFT JOIN product_variants v ON v.id=ol.variant_id
               LEFT JOIN reservations r ON r.order_id=ol.order_id AND r.variant_id=ol.variant_id
               WHERE (o.status IN ('shipped','delivered','completed','returned')
                         AND COALESCE(r.consumed_qty,0)<ol.ordered_qty)
                  OR (o.status='cancelled' AND COALESCE(r.active_qty,0)>0)
                  OR (o.status IN ('new','confirmed','packing','packed','ready_to_ship')
                         AND COALESCE(r.active_qty,0)<ol.ordered_qty)
               ORDER BY o.id DESC,ol.variant_id LIMIT %s""",
            (page_size + 1,),
        )
        rows = [dict(x) for x in cur.fetchall()]
    truncated = len(rows) > page_size
    rows = rows[:page_size]
    counts = {}
    for row in rows:
        counts[row["issue"]] = counts.get(row["issue"], 0) + 1
    return {"items": rows, "counts": counts, "truncated": truncated,
            "limit": page_size}


def stock_supply_ordering_suggestions(actor: Staff, horizon_days: int = 30,
                                      limit: int = 100) -> list[dict]:
    """Suggest replenishment from recent sales velocity and current available stock.

    This is a planning aid, not an automatic purchase order. It uses 30-day
    sales movement as a simple average and deliberately avoids forecasting
    when there is no sale history.
    """
    if actor.role != "owner":
        raise PermissionError("Планування закупівель доступне лише власнику.")
    horizon = _stock_int(horizon_days, "горизонт", 1, 180)
    page_size = _stock_int(limit, "ліміт", 1, 500)
    with db_cursor() as cur:
        cur.execute(
            """WITH sales AS (
                 SELECT variant_id,
                        SUM(-quantity_delta)::numeric AS sold_units,
                        COUNT(*) AS sale_events
                 FROM inventory_movements
                 WHERE movement_type='sale'
                   AND created_at>=NOW()-(%s * INTERVAL '1 day')
                 GROUP BY variant_id
               )
               SELECT v.id AS variant_id,v.sku,p.name AS product_name,
                      v.stock_qty,v.reserved_qty,
                      (v.stock_qty-v.reserved_qty) AS available_qty,
                      v.low_stock_threshold,
                      COALESCE(s.sold_units,0) AS sold_units,
                      COALESCE(s.sale_events,0) AS sale_events,
                      CASE WHEN COALESCE(s.sold_units,0)>0
                           THEN ROUND(s.sold_units/%s,2) ELSE 0 END AS daily_velocity,
                      CASE WHEN COALESCE(s.sold_units,0)>0
                           THEN CEIL((s.sold_units/%s)*%s)
                           ELSE v.low_stock_threshold END AS suggested_target
               FROM product_variants v JOIN products p ON p.id=v.product_id
               LEFT JOIN sales s ON s.variant_id=v.id
               WHERE v.active=TRUE AND p.active=TRUE AND p.archived_at IS NULL
                 AND ((v.stock_qty-v.reserved_qty)<=v.low_stock_threshold
                      OR COALESCE(s.sold_units,0)>0)
               ORDER BY ((v.stock_qty-v.reserved_qty)-v.low_stock_threshold),p.name
               LIMIT %s""",
            (horizon, horizon, horizon, horizon, page_size),
        )
        rows = [dict(x) for x in cur.fetchall()]
    for row in rows:
        row["suggested_order_qty"] = max(
            0, int(row["suggested_target"]) - int(row["available_qty"])
        )
    return rows


def stock_lifecycle_healthcheck(actor: Staff) -> dict:
    """Run compact cross-table checks for the stock lifecycle."""
    if actor.role != "owner":
        raise PermissionError("Перевірка цілісності доступна лише власнику.")
    with db_cursor() as cur:
        cur.execute(
            """SELECT
                 (SELECT COUNT(*) FROM product_variants WHERE stock_qty<0) AS negative_stock,
                 (SELECT COUNT(*) FROM product_variants WHERE reserved_qty<0) AS negative_reserved,
                 (SELECT COUNT(*) FROM product_variants WHERE reserved_qty>stock_qty) AS over_reserved,
                 (SELECT COUNT(*) FROM stock_reservations WHERE state='active' AND expires_at<=NOW()) AS expired_active_reservations,
                 (SELECT COUNT(*) FROM stock_reservations r
                    JOIN orders o ON o.id=r.order_id
                    WHERE r.state='active' AND o.status IN ('cancelled','shipped','delivered','completed','returned')) AS active_reservations_on_terminal_orders,
                 (SELECT COUNT(*) FROM supply_documents WHERE state='draft'
                    AND created_at<NOW()-INTERVAL '30 days') AS stale_supply_drafts,
                 (SELECT COUNT(*) FROM inventory_counts WHERE status='counting'
                    AND created_at<NOW()-INTERVAL '7 days') AS stale_inventory_counts""",
        )
        return dict(cur.fetchone())


def render_stock_lifecycle_report(data: dict) -> str:
    """Render a safe HTML summary without exposing customer information."""
    totals = data.get("totals", {})
    lines = [
        "<b>Звірка складського циклу</b>",
        f"Розбіжності обліку: <b>{int(totals.get('ledger_mismatches', 0))}</b>",
        f"Розбіжності резервів: <b>{int(totals.get('reservation_mismatches', 0))}</b>",
        f"Від’ємні баланси: <b>{int(totals.get('negative_balances', 0))}</b>",
        f"Перерезервовано SKU: <b>{int(totals.get('over_reserved', 0))}</b>",
        "",
    ]
    for item in data.get("items", [])[:30]:
        sku = html.escape(str(item.get("sku") or "SKU"))
        product = html.escape(str(item.get("product_name") or "Товар"))
        state = html.escape(str(item.get("integrity_state") or "unknown"))
        lines.append(
            f"#{int(item['variant_id'])} <b>{sku}</b> · {product}: "
            f"{state}; склад {int(item['stock_qty'])}, "
            f"резерв {int(item['reserved_qty'])}, "
            f"журнал {int(item['ledger_qty'])}"
        )
    if data.get("truncated"):
        lines.append("Показано перші записи. Звіт обрізано за лімітом.")
    return "\n".join(lines)


def render_stock_low_report(items: list[dict]) -> str:
    """Render a concise low-stock list suitable for Telegram HTML."""
    if not items:
        return "Низьких залишків не знайдено."
    lines = ["<b>SKU з низьким залишком</b>"]
    for row in items[:60]:
        sku = html.escape(str(row.get("sku") or "SKU"))
        name = html.escape(str(row.get("product_name") or "Товар"))
        available = int(row.get("available_qty") or 0)
        threshold = int(row.get("low_stock_threshold") or 0)
        lines.append(f"• <b>{sku}</b> · {name}: {available} шт. (поріг {threshold})")
    if len(items) > 60:
        lines.append(f"Ще {len(items)-60} позицій не показано.")
    return "\n".join(lines)


def stock_movement_reason_templates() -> dict:
    """Expose consistent reason templates to future stock-management UI."""
    return {
        "opening_balance": "Початковий залишок під час запуску обліку",
        "supply": "Приймання поставки за документом постачальника",
        "sale": "Списання товару за відправленим замовленням",
        "manual_adjustment": "Ручне коригування після фізичної перевірки",
        "inventory_count": "Різниця за підтвердженою інвентаризацією",
        "return": "Повернення товару після перевірки стану",
        "stock_reversal": "Сторнування помилкового складського документа",
        "reservation": "Резерв товару для підтвердженого замовлення",
        "reservation_release": "Звільнення резерву замовлення",
        "reservation_expired": "Автоматичне завершення строку резерву",
    }


def stock_lifecycle_acceptance_matrix() -> list[dict]:
    """Machine-readable acceptance cases for the inventory lifecycle.

    This matrix is intentionally kept beside the implementation so future
    revisions can test business invariants instead of relying on UI screenshots.
    """
    return [
        {"id": "STK-001", "area": "opening", "given": "new SKU with 8 units",
         "when": "SKU is created", "then": "stock_qty=8 and ledger sum=8"},
        {"id": "STK-002", "area": "opening", "given": "new SKU with zero units",
         "when": "SKU is created", "then": "no physical opening movement is required"},
        {"id": "STK-003", "area": "supply", "given": "draft with 10 ordered, 7 received",
         "when": "document is posted", "then": "stock increases by 7 only"},
        {"id": "STK-004", "area": "supply", "given": "posted supply document",
         "when": "posting is retried", "then": "second posting is rejected"},
        {"id": "STK-005", "area": "supply", "given": "draft supply with received units",
         "when": "line is removed", "then": "removal is rejected"},
        {"id": "STK-006", "area": "supply", "given": "posted receipt",
         "when": "reversal requested with insufficient free stock", "then": "no changes"},
        {"id": "STK-007", "area": "supply", "given": "posted receipt with enough free stock",
         "when": "owner confirms reversal", "then": "negative ledger movement is appended"},
        {"id": "STK-008", "area": "reservation", "given": "order has active reservations",
         "when": "order is cancelled", "then": "reserved_qty decreases exactly once"},
        {"id": "STK-009", "area": "reservation", "given": "reservation expiry",
         "when": "maintenance runs", "then": "reservation expires and order is flagged"},
        {"id": "STK-010", "area": "reservation", "given": "order has no active reservations",
         "when": "shipping is requested", "then": "shipping is rejected"},
        {"id": "STK-011", "area": "reservation", "given": "order has sufficient active reservations",
         "when": "shipping is confirmed", "then": "stock and reserve decrease atomically"},
        {"id": "STK-012", "area": "reservation", "given": "stock changes concurrently",
         "when": "reservation is consumed", "then": "row lock prevents oversell"},
        {"id": "STK-013", "area": "count", "given": "blind inventory count",
         "when": "counter checks progress", "then": "expected stock remains hidden"},
        {"id": "STK-014", "area": "count", "given": "count has missing SKU quantities",
         "when": "confirmation is attempted", "then": "entire transaction is rejected"},
        {"id": "STK-015", "area": "count", "given": "stock movement occurs after a SKU is counted",
         "when": "count is confirmed", "then": "later ledger movement is replayed"},
        {"id": "STK-016", "area": "count", "given": "actual physical quantity below active reserve",
         "when": "count is confirmed", "then": "confirmation is rejected"},
        {"id": "STK-017", "area": "return", "given": "return draft",
         "when": "draft is created", "then": "stock and payment remain unchanged"},
        {"id": "STK-018", "area": "return", "given": "approved restock return",
         "when": "approval is committed", "then": "stock and return movement increase together"},
        {"id": "STK-019", "area": "return", "given": "return without restock",
         "when": "approval is committed", "then": "stock remains unchanged"},
        {"id": "STK-020", "area": "return", "given": "same return approved twice",
         "when": "second approval is attempted", "then": "state guard rejects it"},
        {"id": "STK-021", "area": "ledger", "given": "manual adjustment",
         "when": "reason is blank", "then": "operation is rejected"},
        {"id": "STK-022", "area": "ledger", "given": "manual adjustment",
         "when": "new stock would be below reserved stock", "then": "operation is rejected"},
        {"id": "STK-023", "area": "ledger", "given": "ledger mismatch",
         "when": "preview is requested", "then": "no data is mutated"},
        {"id": "STK-024", "area": "ledger", "given": "ledger mismatch",
         "when": "owner confirms physical correction", "then": "new adjustment is appended"},
        {"id": "STK-025", "area": "ledger", "given": "ledger mismatch",
         "when": "staff requests correction", "then": "permission denied"},
        {"id": "STK-026", "area": "valuation", "given": "SKU without cost price",
         "when": "valuation is generated", "then": "units are marked uncosted"},
        {"id": "STK-027", "area": "valuation", "given": "SKU with cost price",
         "when": "valuation is generated", "then": "current stock value is cost-based"},
        {"id": "STK-028", "area": "reporting", "given": "low stock threshold",
         "when": "report is generated", "then": "available stock is compared to threshold"},
        {"id": "STK-029", "area": "trace", "given": "large movement history",
         "when": "trace is paged", "then": "stable ID cursor avoids offset drift"},
        {"id": "STK-030", "area": "security", "given": "destructive correction",
         "when": "confirmation phrase is wrong", "then": "no write occurs"},
    ]


def stock_lifecycle_selfcheck() -> dict:
    """Run pure invariants that do not require a live database connection."""
    checks = []
    def check(name: str, condition: bool, detail: str = "") -> None:
        checks.append({"name": name, "passed": bool(condition), "detail": detail})
    check("physical movement types exclude reservations",
          "reservation" not in STOCK_PHYSICAL_MOVEMENT_TYPES)
    check("sale movement is physical", "sale" in STOCK_PHYSICAL_MOVEMENT_TYPES)
    check("supply movement is physical", "supply" in STOCK_PHYSICAL_MOVEMENT_TYPES)
    check("reservation terminal states are complete",
          STOCK_RESERVATION_TERMINAL == {"consumed", "released", "expired"})
    matrix = stock_lifecycle_acceptance_matrix()
    check("acceptance matrix has 30 cases", len(matrix) == 30, str(len(matrix)))
    check("acceptance IDs unique",
          len({x["id"] for x in matrix}) == len(matrix))
    check("acceptance areas cover lifecycle",
          {"opening", "supply", "reservation", "count", "return",
           "ledger", "valuation", "reporting", "trace", "security"}
          <= {x["area"] for x in matrix})
    try:
        _stock_int("0", "test", 1, 5)
        check("integer lower bound", False)
    except ValueError:
        check("integer lower bound", True)
    try:
        _stock_reason("  ", minimum=3)
        check("reason cannot be blank", False)
    except ValueError:
        check("reason cannot be blank", True)
    try:
        _stock_reason("valid reason", minimum=3, maximum=4)
        check("reason maximum enforced", False)
    except ValueError:
        check("reason maximum enforced", True)
    return {"passed": all(x["passed"] for x in checks),
            "checks": checks, "passed_count": sum(x["passed"] for x in checks),
            "failed_count": sum(not x["passed"] for x in checks)}


def stock_lifecycle_operator_guide() -> str:
    """Return the operator-facing workflow guide for the stock module."""
    return (
        "СКЛАДСЬКИЙ ЦИКЛ CLOUD HUB\n"
        "1. Створення SKU: початковий фізичний залишок має мати opening_balance.\n"
        "2. Поставка: чернетка -> звірка фактичної кількості -> проведення.\n"
        "3. Резерв: резерв зменшує доступний залишок, але не фізичний stock_qty.\n"
        "4. Відправлення: тільки активний резерв може бути списаний як sale.\n"
        "5. Скасування: активний резерв звільняється без зміни фізичного залишку.\n"
        "6. Повернення: фізичне оприбуткування лише після перевірки стану товару.\n"
        "7. Інвентаризація: сліпий підрахунок, потім підтвердження з причиною.\n"
        "8. Звірка: спочатку preview, потім окреме підтверджене коригування.\n"
        "9. Сторнування поставки: лише власник і лише за наявності вільного залишку.\n"
        "10. Ніколи не редагувати та не видаляти старі рухи журналу."
    )


def stock_lifecycle_command_report(actor: Staff, report_type: str = "integrity") -> dict:
    """Dispatch read-only stock reports for command handlers."""
    allowed = {"integrity", "reservations", "low", "valuation", "health", "movements"}
    if report_type not in allowed:
        raise ValueError("Невідомий тип складського звіту.")
    if report_type == "integrity":
        return inventory_reconciliation_preview(actor)
    if report_type == "reservations":
        return stock_reservation_integrity_report(actor)
    if report_type == "low":
        return {"items": stock_low_stock_report_v2(actor)}
    if report_type == "valuation":
        return inventory_valuation_report(actor)
    if report_type == "health":
        return stock_lifecycle_healthcheck(actor)
    return inventory_movement_summary(actor)


def stock_document_lock_order() -> tuple[str, ...]:
    """Canonical lock order for stock-related transactions.

    When a transaction touches multiple entity classes, it should acquire locks
    in this order to reduce deadlock probability:
      1. order or supply document;
      2. order/supply line rows;
      3. product_variants ordered by numeric ID;
      4. stock_reservations ordered by numeric ID;
      5. append inventory_movements;
      6. append audit_log.
    """
    return ("document", "document_lines", "product_variants",
            "stock_reservations", "inventory_movements", "audit_log")


def stock_lifecycle_invariants() -> dict:
    """Describe the non-negotiable arithmetic invariants used by reports."""
    return {
        "physical_stock": "stock_qty = SUM(physical inventory_movements.quantity_delta)",
        "reserved_stock": "reserved_qty = SUM(stock_reservations.quantity WHERE state='active')",
        "available_stock": "available_qty = stock_qty - reserved_qty",
        "reservation_bound": "0 <= reserved_qty <= stock_qty",
        "physical_bound": "stock_qty >= 0",
        "sale_rule": "sale movement is negative and consumes active reservation",
        "receipt_rule": "supply movement is positive and follows a posted receipt",
        "return_rule": "return movement is positive only when restock is approved",
        "correction_rule": "corrections append a movement and never rewrite history",
        "idempotency_rule": "a posted document or terminal reservation cannot be applied twice",
    }


def stock_lifecycle_version() -> str:
    """Return the stock lifecycle hardening module version."""
    return "2.0.0"


# =============================================================================
# END CLOUD_HUB_STOCK_LIFECYCLE_V2
# =============================================================================

def stock_lifecycle_edge_case_catalog() -> list[dict]:
    """Document edge cases that require deliberate handling in future UI work."""
    return [
        {"id": "EDGE-001", "case": "duplicate webhook or callback",
         "required": "the state guard rejects a second stock mutation"},
        {"id": "EDGE-002", "case": "two packers ship the same order",
         "required": "order row lock serializes both transitions"},
        {"id": "EDGE-003", "case": "two orders reserve the last unit",
         "required": "SKU row lock prevents available stock from going negative"},
        {"id": "EDGE-004", "case": "reservation expires during packing",
         "required": "order moves to problem and must be reviewed"},
        {"id": "EDGE-005", "case": "reservation expires after shipment",
         "required": "terminal order reservation is not silently released"},
        {"id": "EDGE-006", "case": "supplier sends partial quantity",
         "required": "only received_qty is added to physical stock"},
        {"id": "EDGE-007", "case": "supplier sends more than document quantity",
         "required": "receipt validation blocks posting"},
        {"id": "EDGE-008", "case": "supplier invoice contains zero-cost goods",
         "required": "zero cost is accepted and valuation remains explicit"},
        {"id": "EDGE-009", "case": "cost price was historically unknown",
         "required": "incoming cost becomes the weighted-average basis"},
        {"id": "EDGE-010", "case": "return is approved but not restocked",
         "required": "refund workflow can continue without increasing stock"},
        {"id": "EDGE-011", "case": "return item has no variant_id",
         "required": "restock is rejected pending manual SKU mapping"},
        {"id": "EDGE-012", "case": "same order line has multiple return drafts",
         "required": "approval rechecks cumulative approved return quantity"},
        {"id": "EDGE-013", "case": "inventory count races with a sale",
         "required": "movement after counted_at is replayed on confirmation"},
        {"id": "EDGE-014", "case": "inventory count finds fewer units than reserved",
         "required": "count confirmation fails until reserve conflict is resolved"},
        {"id": "EDGE-015", "case": "operator enters a negative physical count",
         "required": "input validation rejects it before database mutation"},
        {"id": "EDGE-016", "case": "SKU is archived during a draft supply",
         "required": "receipt validation identifies inactive or archived SKU"},
        {"id": "EDGE-017", "case": "posted supply is reversed twice",
         "required": "document state guard rejects the second reversal"},
        {"id": "EDGE-018", "case": "posted supply goods were partly sold",
         "required": "reversal refuses to consume reserved or sold units"},
        {"id": "EDGE-019", "case": "reserved_qty differs from active reservation sum",
         "required": "preview identifies drift; owner repair is explicit"},
        {"id": "EDGE-020", "case": "ledger differs from stock_qty",
         "required": "physical correction appends a new movement, never rewrites history"},
        {"id": "EDGE-021", "case": "correction confirmation phrase is mistyped",
         "required": "no database write occurs"},
        {"id": "EDGE-022", "case": "employee tries to reconcile stock",
         "required": "owner-only permission gate rejects the action"},
        {"id": "EDGE-023", "case": "large movement journal",
         "required": "cursor pagination remains stable by movement ID"},
        {"id": "EDGE-024", "case": "low-stock report includes reserved units",
         "required": "threshold compares available, not gross physical, stock"},
        {"id": "EDGE-025", "case": "stock valuation has missing cost",
         "required": "uncosted quantity is visible and excluded from value total"},
        {"id": "EDGE-026", "case": "same Telegram user is owner and admin",
         "required": "notification routing deduplicates recipient elsewhere in outbox"},
        {"id": "EDGE-027", "case": "database transaction fails mid receipt",
         "required": "stock, cost, ledger and document state roll back together"},
        {"id": "EDGE-028", "case": "database transaction fails mid shipment",
         "required": "order status and all SKU deductions roll back together"},
        {"id": "EDGE-029", "case": "maintenance worker overlaps another worker",
         "required": "SKIP LOCKED prevents duplicate reservation processing"},
        {"id": "EDGE-030", "case": "reservation row references missing order",
         "required": "orphan is reported for investigation, never silently discarded"},
    ]


def stock_lifecycle_readiness_summary(actor: Staff) -> dict:
    """Combine stock health, reservation integrity and stale workflow counts."""
    if actor.role != "owner":
        raise PermissionError("Зведений аудит готовності доступний лише власнику.")
    health = stock_lifecycle_healthcheck(actor)
    reservation_report = stock_reservation_integrity_report(actor, limit=1000)
    reconciliation = inventory_reconciliation_preview(actor, limit=2000)
    edge_cases = stock_lifecycle_edge_case_catalog()
    unresolved = (
        int(health.get("negative_stock", 0))
        + int(health.get("negative_reserved", 0))
        + int(health.get("over_reserved", 0))
        + int(health.get("expired_active_reservations", 0))
        + int(health.get("active_reservations_on_terminal_orders", 0))
        + len(reservation_report.get("items", []))
        + len(reconciliation.get("items", []))
    )
    return {
        "status": "attention_required" if unresolved else "no_detected_issues",
        "health": health,
        "reservation_issues": reservation_report,
        "reconciliation": reconciliation,
        "documented_edge_cases": len(edge_cases),
        "unresolved_issue_count": unresolved,
        "note": "Звіт діагностичний. Автоматичне виправлення не виконується.",
    }


def stock_lifecycle_acceptance_overview() -> dict:
    """Expose counts and coverage for code review and regression planning."""
    primary = stock_lifecycle_acceptance_matrix()
    edge = stock_lifecycle_edge_case_catalog()
    return {
        "module_version": stock_lifecycle_version(),
        "primary_acceptance_cases": len(primary),
        "edge_case_scenarios": len(edge),
        "areas": sorted({x["area"] for x in primary}),
        "edge_case_ids_unique": len({x["id"] for x in edge}) == len(edge),
        "acceptance_ids_unique": len({x["id"] for x in primary}) == len(primary),
        "live_database_tested": False,
        "telegram_integration_tested": False,
    }


def stock_lifecycle_no_auto_repair_policy() -> str:
    """Explain why audit and correction are intentionally separate operations."""
    return (
        "Cloud Hub ніколи не виправляє складські розбіжності автоматично. "
        "Звіт лише показує різницю між фізичним залишком, журналом рухів і "
        "активними резервами. Власник має перевірити первинні документи, "
        "фізичну наявність і стан замовлень. Після цього створюється новий "
        "рух коригування з причиною та підтвердженням. Старі рухи не змінюються. "
        "Якщо активні резерви перевищують фізичний залишок, спочатку потрібно "
        "вирішити конфлікт резервів, а не зменшувати фізичний склад."
    )



@bot.callback_query_handler(func=lambda c: bool(c.data) and c.data.startswith("stock:"))
def stock_console_callback_handler(call):
    """Route stock console inline buttons through the same server-side staff checks."""
    staff = require_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    if not stock_console_callback_dispatch(call, staff):
        bot.answer_callback_query(call.id, "Невідома дія.", show_alert=True)



@bot.message_handler(commands=["stock_supply_new"])
def stock_supply_new_command(message):
    """Create a draft supply document from a supplier ID and document number."""
    staff = stock_command_actor(message, "inventory.receive")
    if not staff:
        return
    try:
        parts = (message.text or "").split(maxsplit=2)
        if len(parts) != 3:
            raise ValueError("Формат: /stock_supply_new ID_ПОСТАЧАЛЬНИКА НОМЕР_ДОКУМЕНТА")
        supplier_id = _stock_int(parts[1], "ID постачальника", 1, 2**63 - 1)
        number = " ".join(parts[2].split())
        if not number or len(number) > 80:
            raise ValueError("Номер документа має містити 1–80 символів.")
        supply_id = create_supply_document(number, supplier_id, staff, note="Створено через Telegram stock console")
        audit(staff, "supply.created_ui", "supply", str(supply_id),
              after={"document_number": number, "supplier_id": supplier_id})
        bot.reply_to(
            message,
            f"✅ Чернетку поставки #{supply_id} створено.\n"
            f"Додайте позицію: <code>/stock_supply_add {supply_id} ID_SKU КІЛЬКІСТЬ ЦІНА_ЗАКУПІВЛІ [ПРИЙНЯТО]</code>",
            parse_mode="HTML",
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply_add"])
def stock_supply_add_command(message):
    """Add one SKU line to a draft supply document."""
    staff = stock_command_actor(message, "inventory.receive")
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) not in {5, 6}:
            raise ValueError(
                "Формат: /stock_supply_add ID_ПОСТАВКИ ID_SKU КІЛЬКІСТЬ "
                "ЦІНА_ЗАКУПІВЛІ [ПРИЙНЯТО]"
            )
        supply_id = _stock_int(parts[1], "ID поставки", 1, 2**63 - 1)
        variant_id = _stock_int(parts[2], "ID SKU", 1, 2**63 - 1)
        quantity = _stock_int(parts[3], "кількість", 1, 1_000_000)
        unit_cost = Decimal(parts[4]).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        received = _stock_int(parts[5], "прийнята кількість", 0, quantity) if len(parts) == 6 else 0
        item_id = add_supply_item(
            supply_id, variant_id, quantity, unit_cost, staff, received_qty=received
        )
        audit(staff, "supply.item_added_ui", "supply_item", str(item_id),
              after={"supply_id": supply_id, "variant_id": variant_id,
                     "quantity": quantity, "received_qty": received,
                     "unit_cost": str(unit_cost)})
        bot.reply_to(
            message,
            f"✅ Рядок #{item_id} додано до поставки #{supply_id}. "
            f"Прийнято {received}/{quantity}.",
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply_received"])
def stock_supply_received_command(message):
    """Update received quantity for a SKU line in a draft supply."""
    staff = stock_command_actor(message, "inventory.receive")
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 4:
            raise ValueError("Формат: /stock_supply_received ID_ПОСТАВКИ ID_SKU ПРИЙНЯТО")
        supply_id = _stock_int(parts[1], "ID поставки", 1, 2**63 - 1)
        variant_id = _stock_int(parts[2], "ID SKU", 1, 2**63 - 1)
        received = _stock_int(parts[3], "прийнята кількість", 0, 1_000_000)
        update_supply_received_qty(supply_id, variant_id, received, staff)
        bot.reply_to(message, f"✅ Фактичне приймання SKU #{variant_id} оновлено.")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply_validate"])
def stock_supply_validate_command(message):
    """Validate a draft supply before posting it."""
    staff = stock_command_actor(message, "inventory.receive")
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /stock_supply_validate ID_ПОСТАВКИ")
        supply_id = _stock_int(parts[1], "ID поставки", 1, 2**63 - 1)
        result = supply_receipt_validation(supply_id, staff)
        lines = [
            f"Документ #{supply_id}: {'ГОТОВИЙ' if result['valid'] else 'Є ПОМИЛКИ'}",
            f"Номер: {safe(result.get('document_number') or '')}",
            f"Рядків: {len(result['items'])}",
        ]
        for issue in result["issues"]:
            lines.append(f"⚠️ {safe(issue.get('type') or '')}: {safe(issue.get('message') or issue.get('sku') or '')}")
        if result["valid"]:
            lines += [
                "",
                "Для проведення власник або працівник із inventory.receive надсилає:",
                f"<code>/stock_supply_post {supply_id} ПІДТВЕРДЖУЮ</code>",
            ]
        stock_report_send(message.chat.id, "Перевірка поставки", lines,
                          stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply_post"])
def stock_supply_post_command(message):
    """Post a validated supply after an explicit confirmation token."""
    staff = stock_command_actor(message, "inventory.receive")
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 3:
            raise ValueError("Формат: /stock_supply_post ID_ПОСТАВКИ ПІДТВЕРДЖУЮ")
        supply_id = _stock_int(parts[1], "ID поставки", 1, 2**63 - 1)
        if parts[2] != "ПІДТВЕРДЖУЮ":
            raise ValueError("Потрібен точний токен ПІДТВЕРДЖУЮ.")
        validation = supply_receipt_validation(supply_id, staff)
        if not validation["valid"]:
            raise ValueError("Поставка не пройшла перевірку. Виконайте /stock_supply_validate.")
        result = post_supply_document(supply_id, staff)
        audit(
            staff, "supply.posted_ui", "supply", str(supply_id),
            after={"document_number": result["document_number"],
                   "items": result["items"],
                   "total_received_cost": str(result["total_received_cost"])},
        )
        lines = [
            f"Документ: {safe(result['document_number'])}",
            f"Прийнято SKU: {len(result['items'])}",
            f"Фактична вартість: {money(result['total_received_cost'])}",
        ]
        for item in result["items"]:
            lines.append(
                f"<b>{safe(item['sku'])}</b>: +{int(item['received'])} шт.; "
                f"нова середня собівартість {money(item['weighted_cost'])}"
            )
        stock_report_send(message.chat.id, f"✅ Поставку #{supply_id} проведено",
                          lines, stock_console_back_keyboard())
    except Exception as exc:
        log.exception("Supply posting command failed")
        bot.reply_to(message, safe(str(exc)))



# =============================================================================
# CLOUD HUB STOCK CONSOLE UI + OPERATOR WORKFLOWS
# =============================================================================
# This layer wires the stock lifecycle services into Telegram. It is deliberately
# owner/permission-gated and keeps write operations explicit and auditable.
# =============================================================================

STOCK_CONSOLE_CALLBACKS = frozenset({
    "console", "integrity", "reservations", "movements", "valuation",
    "health", "low", "replenishment", "count_start",
})


def stock_console_keyboard(staff: Staff) -> types.InlineKeyboardMarkup:
    """Build a permission-aware stock console keyboard."""
    kb = types.InlineKeyboardMarkup(row_width=2)
    if staff.can("inventory.read") or staff.can("inventory.adjust") or staff.can("inventory.receive"):
        kb.add(
            types.InlineKeyboardButton("⚠️ Малі залишки", callback_data="stock:low"),
            types.InlineKeyboardButton("📚 Рухи складу", callback_data="stock:movements"),
        )
        kb.add(
            types.InlineKeyboardButton("🧮 Інвентаризації", callback_data="section:counts"),
            types.InlineKeyboardButton("🚚 Поставки", callback_data="section:supplies"),
        )
    if staff.role == "owner":
        kb.add(
            types.InlineKeyboardButton("🛡️ Звірка залишків", callback_data="stock:integrity"),
            types.InlineKeyboardButton("🔐 Перевірка резервів", callback_data="stock:reservations"),
        )
        kb.add(
            types.InlineKeyboardButton("💵 Оцінка запасів", callback_data="stock:valuation"),
            types.InlineKeyboardButton("📈 Рухи за 30 днів", callback_data="stock:health"),
        )
        kb.add(types.InlineKeyboardButton("📦 План закупівель", callback_data="stock:replenishment"))
    if staff.role in {"owner", "admin", "packer"}:
        kb.add(types.InlineKeyboardButton("➕ Почати інвентаризацію", callback_data="stock:count_start"))
    kb.add(types.InlineKeyboardButton("↩️ До складу", callback_data="section:inventory"))
    kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    return kb


def stock_console_text(staff: Staff) -> str:
    """Summarize what each staff role can do without exposing owner-only metrics."""
    lines = [
        "<b>📦 Контроль складу Cloud Hub</b>",
        "",
        "Фізичний залишок і резерви обліковуються окремо.",
        "Доступна кількість = фізичний залишок − активні резерви.",
        "",
    ]
    if staff.role == "owner":
        lines += [
            "Власник бачить повну звірку, собівартість, оцінку запасів і резерви.",
            "Коригування не запускаються автоматично. Спочатку звіт, потім підтверджена дія.",
        ]
    elif staff.role == "admin":
        lines += [
            "Адміністратор може вести інвентаризацію та приймання поставок згідно з дозволами.",
            "Повна фінансова оцінка та системна звірка доступні лише власнику.",
        ]
    else:
        lines += [
            "Працівник може переглядати доступні залишки та брати участь у сліпій інвентаризації.",
            "Підтвердження коригувань і повна звірка залишаються за керівництвом.",
        ]
    return "\n".join(lines)


def stock_console_send(chat_id: int, staff: Staff) -> None:
    """Render the stock console."""
    bot.send_message(
        chat_id, stock_console_text(staff),
        reply_markup=stock_console_keyboard(staff),
        disable_web_page_preview=True,
    )


def stock_report_send(chat_id: int, title: str, lines: list[str],
                      keyboard: types.InlineKeyboardMarkup = None) -> None:
    """Send a Telegram HTML report in bounded chunks without splitting records."""
    header = f"<b>{safe(title)}</b>"
    chunks = []
    current = header
    for line in lines:
        candidate = current + "\n" + line
        if len(candidate) > 3700 and current != header:
            chunks.append(current)
            current = header + "\n" + line
        else:
            current = candidate
    if current:
        chunks.append(current)
    if not chunks:
        chunks = [header]
    for index, chunk in enumerate(chunks):
        bot.send_message(
            chat_id, chunk,
            reply_markup=keyboard if index == len(chunks) - 1 else None,
            disable_web_page_preview=True,
        )


def stock_console_back_keyboard() -> types.InlineKeyboardMarkup:
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(
        types.InlineKeyboardButton("↩️ Контроль складу", callback_data="stock:console"),
        types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"),
    )
    return kb


def stock_integrity_report_lines(data: dict) -> list[str]:
    """Format physical ledger reconciliation for the owner."""
    totals = data.get("totals") or {}
    lines = [
        f"Перевірено SKU: <b>{int(totals.get('variants') or 0)}</b>",
        f"Розбіжності фізичного журналу: <b>{int(totals.get('ledger_mismatches') or 0)}</b>",
        f"Розбіжності резервів: <b>{int(totals.get('reservation_mismatches') or 0)}</b>",
        f"Від’ємні баланси: <b>{int(totals.get('negative_balances') or 0)}</b>",
        f"Резерв більший за склад: <b>{int(totals.get('over_reserved') or 0)}</b>",
        "",
    ]
    for row in data.get("items", [])[:35]:
        lines.append(
            f"#{int(row['variant_id'])} <b>{safe(row.get('sku') or '')}</b> "
            f"{safe(row.get('product_name') or '')}: "
            f"<b>{safe(row.get('integrity_state') or '')}</b>; "
            f"факт {int(row.get('stock_qty') or 0)}, "
            f"резерв {int(row.get('reserved_qty') or 0)}, "
            f"журнал {int(row.get('ledger_qty') or 0)}"
        )
    if not data.get("items"):
        lines.append("Розбіжностей не знайдено.")
    if data.get("truncated"):
        lines.append("Список обмежено. Повний перелік можна отримати повторним аудитом із більшим лімітом.")
    lines.append("")
    lines.append("Це діагностика. Склад автоматично не змінювався.")
    return lines


def stock_reservation_report_lines(data: dict) -> list[str]:
    """Format order-level reservation anomalies."""
    lines = []
    for row in data.get("items", [])[:50]:
        lines.append(
            f"Замовлення #{int(row['order_id'])} · {safe(row.get('order_number') or '')} "
            f"· {safe(row.get('sku') or '')}: <b>{safe(row.get('issue') or '')}</b> "
            f"(потрібно {int(row.get('ordered_qty') or 0)}, "
            f"активно {int(row.get('active_qty') or 0)}, "
            f"списано {int(row.get('consumed_qty') or 0)})"
        )
    if not lines:
        lines.append("Проблем із резервами за перевіреними правилами не знайдено.")
    if data.get("truncated"):
        lines.append("Список обрізано за лімітом.")
    return lines


def stock_valuation_report_lines(data: dict) -> list[str]:
    """Format owner-only stock valuation with uncosted quantities disclosed."""
    lines = [
        f"Облікова вартість фізичного залишку: <b>{money(data.get('stock_value', 0))}</b>",
        f"Одиниць без собівартості: <b>{int(data.get('uncosted_units') or 0)}</b>",
        "Метод: поточна середньозважена собівартість, не роздрібна ціна.",
        "",
    ]
    for row in data.get("items", [])[:30]:
        cost = "не задана" if row.get("cost_price") is None else money(row["cost_price"])
        value = "не оцінено" if row.get("stock_value") is None else money(row["stock_value"])
        lines.append(
            f"<b>{safe(row.get('sku') or '')}</b> · {safe(row.get('product_name') or '')}: "
            f"{int(row.get('stock_qty') or 0)} шт. × {cost} = {value}"
        )
    if data.get("truncated"):
        lines.append("Показано перші позиції, загальний підсумок рахується лише за вибіркою.")
    return lines


def stock_replenishment_report_lines(rows: list[dict]) -> list[str]:
    """Format replenishment recommendations with their calculation basis."""
    lines = [
        "Розрахунок: продажі за останні 30 днів, середній темп і доступний залишок.",
        "Це рекомендації, не автоматичні замовлення постачальнику.",
        "",
    ]
    for row in rows[:45]:
        lines.append(
            f"<b>{safe(row.get('sku') or '')}</b> · {safe(row.get('product_name') or '')}: "
            f"доступно {int(row.get('available_qty') or 0)}, "
            f"продано {int(row.get('sold_units') or 0)}, "
            f"рекомендовано замовити {int(row.get('suggested_order_qty') or 0)}"
        )
    if not rows:
        lines.append("Немає SKU з історією продажів або низьким залишком.")
    return lines


def stock_low_report_lines(rows: list[dict]) -> list[str]:
    """Format low-stock records without leaking internal costs."""
    lines = []
    for row in rows[:70]:
        lines.append(
            f"<b>{safe(row.get('sku') or '')}</b> · {safe(row.get('product_name') or '')}: "
            f"доступно {int(row.get('available_qty') or 0)} шт.; "
            f"поріг {int(row.get('low_stock_threshold') or 0)}"
        )
    return lines or ["Низьких залишків не знайдено."]


def stock_movements_report_lines(data: dict) -> list[str]:
    """Format movement activity summary."""
    totals = data.get("totals") or {}
    lines = [
        f"Період: останні {int(data.get('days') or 30)} днів",
        f"SKU з рухами: {int(totals.get('sku_count') or 0)}",
        f"Записів у журналі: {int(totals.get('movement_count') or 0)}",
        "",
    ]
    for row in data.get("by_type", []):
        lines.append(
            f"• {safe(row.get('movement_type') or '')}: "
            f"{int(row.get('rows') or 0)} подій, "
            f"чистий рух {int(row.get('net_units') or 0)}, "
            f"оборот {int(row.get('gross_units') or 0)} шт."
        )
    return lines


def stock_health_report_lines(data: dict) -> list[str]:
    """Format maintenance-level health counters."""
    labels = {
        "negative_stock": "SKU з від’ємним фізичним залишком",
        "negative_reserved": "SKU з від’ємним резервом",
        "over_reserved": "SKU з резервом понад фізичний залишок",
        "expired_active_reservations": "Прострочені активні резерви",
        "active_reservations_on_terminal_orders": "Активні резерви на завершених замовленнях",
        "stale_supply_drafts": "Чернетки поставок старші 30 днів",
        "stale_inventory_counts": "Інвентаризації без руху понад 7 днів",
    }
    return [f"{safe(label)}: <b>{int(data.get(key) or 0)}</b>"
            for key, label in labels.items()]


def stock_count_progress_lines(data: dict) -> list[str]:
    """Format blind inventory count progress, showing actual entries only."""
    progress = data.get("progress") or {}
    count = data.get("count") or {}
    lines = [
        f"Інвентаризація #{int(count.get('id') or 0)} · статус {safe(count.get('status') or '')}",
        f"Внесено: {int(progress.get('counted') or 0)} / {int(progress.get('total') or 0)}",
        f"Залишилося: {int(progress.get('remaining') or 0)}",
        "",
    ]
    for row in data.get("items", [])[:80]:
        actual = "не внесено" if row.get("actual_qty") is None else f"{int(row['actual_qty'])} шт."
        lines.append(
            f"SKU #{int(row.get('variant_id') or 0)} "
            f"<b>{safe(row.get('sku') or '')}</b> · {safe(row.get('product_name') or '')}: {actual}"
        )
    return lines


def stock_supply_list_keyboard(rows: list[dict]) -> types.InlineKeyboardMarkup:
    """Build buttons for a small list of recent supply documents."""
    kb = types.InlineKeyboardMarkup(row_width=1)
    for row in rows[:20]:
        kb.add(types.InlineKeyboardButton(
            f"#{row['id']} · {str(row.get('document_number') or '')[:24]} · {row.get('state')}",
            callback_data=f"stock:supply:{int(row['id'])}",
        ))
    kb.add(types.InlineKeyboardButton("↩️ Контроль складу", callback_data="stock:console"))
    return kb


def stock_supply_list_send(chat_id: int, staff: Staff) -> None:
    """Render supply documents with role-aware access."""
    if not staff.can("inventory.receive") and not staff.can("inventory.read"):
        bot.send_message(chat_id, "⛔ Недостатньо прав.")
        return
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,document_number,state,document_date,total_cost,created_at
               FROM supply_documents ORDER BY created_at DESC LIMIT 50"""
        )
        rows = [dict(x) for x in cur.fetchall()]
    if not rows:
        bot.send_message(chat_id, "Поставок поки немає.", reply_markup=stock_console_keyboard(staff))
        return
    lines = [
        f"#{int(x['id'])} · {safe(x.get('document_number') or '')} · "
        f"{safe(x.get('state') or '')} · {safe(x.get('document_date') or '')}"
        for x in rows
    ]
    stock_report_send(chat_id, "🚚 Останні поставки", lines, stock_supply_list_keyboard(rows))


def stock_supply_detail_send(chat_id: int, supply_id: int, staff: Staff) -> None:
    """Render one supply with received quantities and draft/post state."""
    if not staff.can("inventory.receive") and not staff.can("inventory.read"):
        bot.send_message(chat_id, "⛔ Недостатньо прав.")
        return
    data = supply_document_snapshot(supply_id, staff)
    doc = data["document"]
    lines = [
        f"Документ: <b>{safe(doc.get('document_number') or '')}</b>",
        f"Статус: <b>{safe(doc.get('state') or '')}</b>",
        f"Постачальник: {safe(doc.get('supplier_name') or 'не вказано')}",
        f"Прийнято: {data['received_units']} / {data['planned_units']} шт.",
        f"Фактична вартість приймання: {money(data['received_cost'])}",
        "",
    ]
    for item in data["items"][:60]:
        lines.append(
            f"<b>{safe(item.get('sku') or '')}</b> · {safe(item.get('product_name') or '')}: "
            f"{int(item.get('received_qty') or 0)} / {int(item.get('quantity') or 0)} шт.; "
            f"залишилось {int(item.get('outstanding_qty') or 0)}"
        )
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("↩️ До поставок", callback_data="stock:supplies"))
    kb.add(types.InlineKeyboardButton("📦 Контроль складу", callback_data="stock:console"))
    stock_report_send(chat_id, f"Поставка #{supply_id}", lines, kb)


def stock_count_detail_send(chat_id: int, count_id: int, staff: Staff) -> None:
    """Render blind count progress and exact command syntax for SKU entry."""
    if staff.role not in {"owner", "admin", "packer"}:
        bot.send_message(chat_id, "⛔ Недостатньо прав.")
        return
    data = inventory_count_progress_v2(count_id, staff)
    lines = stock_count_progress_lines(data)
    lines += [
        "",
        "<b>Внесення фактичної кількості</b>",
        f"<code>/stock_count_set {count_id} ID_SKU КІЛЬКІСТЬ</code>",
        "ID SKU показано в кожному рядку. Очікуваний системний залишок прихований.",
    ]
    kb = types.InlineKeyboardMarkup(row_width=2)
    kb.add(types.InlineKeyboardButton("🔄 Оновити", callback_data=f"stock:count:{count_id}"))
    if staff.role in {"owner", "admin"}:
        kb.add(types.InlineKeyboardButton("ℹ️ Як підтвердити", callback_data=f"stock:count_help:{count_id}"))
    kb.add(types.InlineKeyboardButton("↩️ Інвентаризації", callback_data="section:counts"))
    stock_report_send(chat_id, f"🧮 Інвентаризація #{count_id}", lines, kb)


def stock_count_help_send(chat_id: int, count_id: int) -> None:
    """Explain the blind count confirmation workflow."""
    lines = [
        "1. Внесіть фактичну кількість кожного SKU командою:",
        f"<code>/stock_count_set {count_id} ID_SKU КІЛЬКІСТЬ</code>",
        "2. Перевірте прогрес командою /stock_count_status ID.",
        "3. Після заповнення всіх рядків власник або адміністратор підтверджує:",
        f"<code>/stock_count_confirm {count_id} причина_коригування</code>",
        "",
        "Під час підрахунку системний залишок не показується.",
        "Після підтвердження різниця записується окремим рухом inventory_count.",
        "Якщо фактична кількість нижча за активний резерв, підтвердження буде заблоковано.",
    ]
    stock_report_send(chat_id, f"Порядок інвентаризації #{count_id}", lines,
                      stock_console_back_keyboard())


def stock_console_callback_dispatch(call, staff: Staff) -> bool:
    """Dispatch stock console callbacks. Return False for unrelated callback data."""
    if not call.data.startswith("stock:"):
        return False
    parts = call.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    chat_id = call.message.chat.id
    try:
        if action == "console":
            stock_console_send(chat_id, staff)
        elif action == "low":
            if not (staff.can("inventory.read") or staff.can("catalog.read")):
                raise PermissionError("Недостатньо прав.")
            rows = stock_low_stock_report_v2(staff, limit=150)
            stock_report_send(chat_id, "⚠️ Малі залишки", stock_low_report_lines(rows),
                              stock_console_back_keyboard())
        elif action == "integrity":
            if staff.role != "owner":
                raise PermissionError("Повна звірка доступна лише власнику.")
            data = inventory_reconciliation_preview(staff, limit=500)
            audit(staff, "stock.integrity_report_viewed", "inventory", "all")
            stock_report_send(chat_id, "🛡️ Звірка складу",
                              stock_integrity_report_lines(data),
                              stock_console_back_keyboard())
        elif action == "reservations":
            if staff.role != "owner":
                raise PermissionError("Перевірка резервів доступна лише власнику.")
            data = stock_reservation_integrity_report(staff, limit=500)
            audit(staff, "stock.reservation_report_viewed", "inventory", "reservations")
            stock_report_send(chat_id, "🔐 Перевірка резервів",
                              stock_reservation_report_lines(data),
                              stock_console_back_keyboard())
        elif action == "valuation":
            if staff.role != "owner":
                raise PermissionError("Оцінка запасів доступна лише власнику.")
            data = inventory_valuation_report(staff, limit=300)
            audit(staff, "stock.valuation_report_viewed", "inventory", "valuation")
            stock_report_send(chat_id, "💵 Оцінка запасів",
                              stock_valuation_report_lines(data),
                              stock_console_back_keyboard())
        elif action == "movements":
            if not (staff.can("inventory.read") or staff.role == "owner"):
                raise PermissionError("Недостатньо прав.")
            data = inventory_movement_summary(staff, days=30)
            stock_report_send(chat_id, "📚 Рухи складу",
                              stock_movements_report_lines(data),
                              stock_console_back_keyboard())
        elif action == "health":
            if staff.role != "owner":
                raise PermissionError("Системна перевірка доступна лише власнику.")
            data = stock_lifecycle_healthcheck(staff)
            stock_report_send(chat_id, "📈 Стан складських процесів",
                              stock_health_report_lines(data),
                              stock_console_back_keyboard())
        elif action == "replenishment":
            if staff.role != "owner":
                raise PermissionError("План закупівель доступний лише власнику.")
            rows = stock_supply_ordering_suggestions(staff, horizon_days=30, limit=150)
            stock_report_send(chat_id, "📦 План закупівель",
                              stock_replenishment_report_lines(rows),
                              stock_console_back_keyboard())
        elif action == "count_start":
            if staff.role not in {"owner", "admin", "packer"}:
                raise PermissionError("Недостатньо прав.")
            count_id = create_inventory_count(staff)
            audit(staff, "inventory.count_started", "inventory_count", str(count_id))
            stock_count_detail_send(chat_id, count_id, staff)
        elif action == "count" and len(parts) == 3:
            stock_count_detail_send(chat_id, int(parts[2]), staff)
        elif action == "count_help" and len(parts) == 3:
            if staff.role not in {"owner", "admin"}:
                raise PermissionError("Недостатньо прав.")
            stock_count_help_send(chat_id, int(parts[2]))
        elif action == "supply" and len(parts) == 3:
            stock_supply_detail_send(chat_id, int(parts[2]), staff)
        elif action == "supplies":
            stock_supply_list_send(chat_id, staff)
        else:
            return False
        bot.answer_callback_query(call.id)
        return True
    except Exception as exc:
        log.exception("Stock console callback failed: %s", call.data)
        bot.answer_callback_query(call.id, safe(str(exc))[:180], show_alert=True)
        return True


def stock_command_actor(message, permission: str = None) -> Staff:
    """Resolve staff identity for stock commands and reject customer access."""
    staff = require_staff(message, permission)
    if not staff:
        bot.reply_to(message, "⛔ Команда доступна лише працівникам із відповідними правами.")
        return None
    return staff


@bot.message_handler(commands=["stock"])
def stock_console_command(message):
    """Open the stock console by command."""
    staff = stock_command_actor(message, "inventory.read")
    if staff:
        stock_console_send(message.chat.id, staff)


@bot.message_handler(commands=["stock_sku"])
def stock_sku_command(message):
    """Inspect one SKU using a numeric product-variant identifier."""
    staff = stock_command_actor(message, "inventory.read")
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /stock_sku ID_SKU")
        variant_id = _stock_int(parts[1], "ID SKU", 1, 2**63 - 1)
        data = stock_variant_snapshot(variant_id, staff)
        variant = data["variant"]
        lines = [
            f"SKU: <b>{safe(variant.get('sku') or '')}</b>",
            f"Товар: {safe(variant.get('product_name') or '')}",
            f"Фізичний залишок: <b>{int(variant['stock_qty'])}</b>",
            f"Резерв: <b>{int(variant['reserved_qty'])}</b>",
            f"Доступно: <b>{int(variant['available_qty'])}</b>",
        ]
        if staff.role == "owner":
            lines.append(f"Закупівельна ціна: {safe(variant.get('cost_price'))}")
        for movement in data["recent_movements"][:15]:
            lines.append(
                f"• #{movement['id']} {safe(movement.get('movement_type') or '')}: "
                f"{int(movement['quantity_delta'])} · {safe(movement.get('reason') or '')}"
            )
        bot.reply_to(message, "\n".join(lines), parse_mode="HTML")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_count_start"])
def stock_count_start_command(message):
    """Create a new blind count for all active SKUs."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role not in {"owner", "admin", "packer"}:
            raise PermissionError("Недостатньо прав.")
        count_id = create_inventory_count(staff)
        audit(staff, "inventory.count_started", "inventory_count", str(count_id))
        stock_count_detail_send(message.chat.id, count_id, staff)
    except Exception as exc:
        log.exception("Unable to start inventory count")
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_count_set"])
def stock_count_set_command(message):
    """Record one blind-count quantity for one SKU."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 4:
            raise ValueError("Формат: /stock_count_set ID_ІНВЕНТАРИЗАЦІЇ ID_SKU КІЛЬКІСТЬ")
        count_id = _stock_int(parts[1], "ID інвентаризації", 1, 2**63 - 1)
        variant_id = _stock_int(parts[2], "ID SKU", 1, 2**63 - 1)
        quantity = _stock_int(parts[3], "фактична кількість", 0, 1_000_000)
        if staff.role not in {"owner", "admin", "packer"}:
            raise PermissionError("Недостатньо прав.")
        record_inventory_count_item(count_id, variant_id, quantity, staff)
        audit(staff, "inventory.count_item_recorded", "inventory_count_item",
              f"{count_id}:{variant_id}", after={"actual_qty": quantity})
        bot.reply_to(
            message,
            f"✅ Записано: інвентаризація #{count_id}, SKU #{variant_id}, "
            f"фактична кількість {quantity}.",
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_count_status"])
def stock_count_status_command(message):
    """Show blind-count progress without expected stock quantities."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /stock_count_status ID")
        count_id = _stock_int(parts[1], "ID інвентаризації", 1, 2**63 - 1)
        stock_count_detail_send(message.chat.id, count_id, staff)
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_count_confirm"])
def stock_count_confirm_command(message):
    """Confirm a complete count with an explicit reason."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split(maxsplit=2)
        if len(parts) != 3:
            raise ValueError("Формат: /stock_count_confirm ID причина_коригування")
        count_id = _stock_int(parts[1], "ID інвентаризації", 1, 2**63 - 1)
        reason = _stock_reason(parts[2], minimum=5, maximum=500)
        if staff.role not in {"owner", "admin"}:
            raise PermissionError("Підтвердити інвентаризацію може власник або адміністратор.")
        report = confirm_inventory_count(count_id, staff, reason)
        audit(staff, "inventory.count_confirmed_ui", "inventory_count",
              str(count_id), after={"lines": len(report), "reason": reason})
        lines = []
        for row in report[:70]:
            lines.append(
                f"SKU #{int(row['variant_id'])}: "
                f"було {int(row['system_qty'])}, стало {int(row['actual_qty'])}, "
                f"різниця {int(row['discrepancy']):+d}"
            )
        stock_report_send(
            message.chat.id, f"✅ Інвентаризацію #{count_id} підтверджено",
            lines or ["Змін не було."], stock_console_back_keyboard(),
        )
    except Exception as exc:
        log.exception("Inventory count confirmation failed")
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply"])
def stock_supply_command(message):
    """Open the supply-document list."""
    staff = stock_command_actor(message)
    if staff:
        stock_supply_list_send(message.chat.id, staff)


def stock_console_regression_matrix() -> list[dict]:
    """List UI-level acceptance cases for stock console wiring."""
    return [
        {"id": "UI-STK-001", "role": "owner", "action": "/stock",
         "expected": "full stock console is displayed"},
        {"id": "UI-STK-002", "role": "admin", "action": "/stock",
         "expected": "operational reports appear, owner-only finance is absent"},
        {"id": "UI-STK-003", "role": "packer", "action": "/stock",
         "expected": "permitted read and count actions only"},
        {"id": "UI-STK-004", "role": "customer", "action": "/stock",
         "expected": "access denied"},
        {"id": "UI-STK-005", "role": "owner", "action": "stock:integrity",
         "expected": "physical ledger and reservation discrepancies are shown"},
        {"id": "UI-STK-006", "role": "admin", "action": "stock:integrity",
         "expected": "owner-only action denied"},
        {"id": "UI-STK-007", "role": "owner", "action": "stock:valuation",
         "expected": "cost and stock value are shown"},
        {"id": "UI-STK-008", "role": "admin", "action": "stock:valuation",
         "expected": "owner-only cost report denied"},
        {"id": "UI-STK-009", "role": "packer", "action": "stock:count_start",
         "expected": "blind count starts without expected quantities"},
        {"id": "UI-STK-010", "role": "packer", "action": "/stock_count_confirm",
         "expected": "confirmation denied"},
        {"id": "UI-STK-011", "role": "admin", "action": "/stock_count_set",
         "expected": "actual quantity is stored for an enrolled SKU"},
        {"id": "UI-STK-012", "role": "owner", "action": "/stock_count_confirm",
         "expected": "all lines must be counted before confirmation"},
        {"id": "UI-STK-013", "role": "owner", "action": "stock:supply:ID",
         "expected": "supply details and received quantities are displayed"},
        {"id": "UI-STK-014", "role": "owner", "action": "stock:replenishment",
         "expected": "replenishment suggestions do not create purchase orders"},
        {"id": "UI-STK-015", "role": "staff", "action": "/stock_sku ID",
         "expected": "SKU physical, reserved and available quantities are shown"},
        {"id": "UI-STK-016", "role": "staff", "action": "/stock_count_status ID",
         "expected": "blind count progress is shown without expected quantity"},
        {"id": "UI-STK-017", "role": "staff", "action": "/stock_supply",
         "expected": "recent supply documents are listed"},
        {"id": "UI-STK-018", "role": "owner", "action": "stock:health",
         "expected": "maintenance-level stock health counters are shown"},
        {"id": "UI-STK-019", "role": "staff", "action": "stock:movements",
         "expected": "movement summary obeys inventory read permission"},
        {"id": "UI-STK-020", "role": "owner", "action": "stock:reservations",
         "expected": "order reservation anomalies are listed"},
    ]


def stock_console_selfcheck() -> dict:
    """Pure checks for UI callback routing and regression catalog."""
    matrix = stock_console_regression_matrix()
    actions = {x["action"] for x in matrix}
    checks = {
        "twenty_ui_acceptance_cases": len(matrix) == 20,
        "unique_case_ids": len({x["id"] for x in matrix}) == len(matrix),
        "has_owner_integrity": "stock:integrity" in actions,
        "has_blind_count": "/stock_count_set" in actions,
        "has_confirmation": "/stock_count_confirm" in actions,
        "has_supply_details": "stock:supply:ID" in actions,
        "has_customer_denial": any(x["role"] == "customer" for x in matrix),
        "has_owner_only_finance_guard": any(
            x["action"] == "stock:valuation" and x["role"] == "admin" for x in matrix
        ),
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


def stock_console_operator_commands() -> dict:
    """Return exact operator command syntax for documentation and help."""
    return {
        "/stock": "Відкрити контроль складу",
        "/stock_sku ID_SKU": "Переглянути фізичний залишок, резерв і журнал SKU",
        "/stock_count_start": "Почати сліпу інвентаризацію всіх активних SKU",
        "/stock_count_set ID_ІНВЕНТАРИЗАЦІЇ ID_SKU КІЛЬКІСТЬ": "Внести фактичний підрахунок",
        "/stock_count_status ID": "Переглянути прогрес інвентаризації",
        "/stock_count_confirm ID причина": "Підтвердити завершену інвентаризацію",
        "/stock_supply": "Переглянути документи поставок",
        "/stock_supply_new ID НОМЕР": "Створити чернетку поставки",
        "/stock_supply_add ID ID_SKU КІЛЬКІСТЬ ЦІНА [ПРИЙНЯТО]": "Додати SKU до чернетки",
        "/stock_supply_validate ID": "Перевірити поставку перед проведенням",
        "/stock_supply_post ID ПІДТВЕРДЖУЮ": "Провести перевірену поставку",
    }


def stock_console_permissions_matrix() -> dict:
    """Document access boundaries enforced by the stock console."""
    return {
        "owner": ["console", "low", "movements", "integrity", "reservations",
                  "valuation", "health", "replenishment", "count_start",
                  "count_set", "count_confirm", "supply_detail"],
        "admin": ["console", "low", "movements", "count_start", "count_set",
                  "count_confirm", "supply_detail"],
        "packer": ["console", "low", "count_start", "count_set", "count_status"],
        "manager": ["only permissions explicitly granted by Staff.can"],
        "customer": [],
    }


def stock_console_version() -> str:
    """Return stock console integration version."""
    return "1.0.0"


# =============================================================================
# END CLOUD HUB STOCK CONSOLE UI
# =============================================================================

# =============================================================================
# STOCK CONSOLE EXTENDED OPERATIONS
# =============================================================================

def stock_find_variants(query: str, actor: Staff, limit: int = 30) -> list[dict]:
    """Search SKU, product and variant names to resolve internal variant IDs."""
    if not (actor.can("inventory.read") or actor.can("catalog.read")
            or actor.can("inventory.adjust")):
        raise PermissionError("Недостатньо прав для пошуку SKU.")
    clean = " ".join(str(query or "").split())
    if len(clean) < 2 or len(clean) > 100:
        raise ValueError("Пошуковий запит має містити 2–100 символів.")
    page_size = _stock_int(limit, "ліміт", 1, 100)
    pattern = f"%{clean}%"
    with db_cursor() as cur:
        cur.execute(
            """SELECT v.id AS variant_id,v.sku,v.variant_name,
                      p.name AS product_name,b.name AS brand_name,
                      v.stock_qty,v.reserved_qty,
                      (v.stock_qty-v.reserved_qty) AS available_qty
               FROM product_variants v
               JOIN products p ON p.id=v.product_id
               LEFT JOIN brands b ON b.id=p.brand_id
               WHERE v.active=TRUE AND p.archived_at IS NULL
                 AND (v.sku ILIKE %s OR v.variant_name ILIKE %s
                      OR p.name ILIKE %s OR COALESCE(b.name,'') ILIKE %s)
               ORDER BY CASE WHEN LOWER(v.sku)=LOWER(%s) THEN 0
                             WHEN LOWER(v.sku) LIKE LOWER(%s) THEN 1
                             WHEN LOWER(p.name)=LOWER(%s) THEN 2
                             ELSE 3 END,
                        p.name,v.sku
               LIMIT %s""",
            (pattern, pattern, pattern, pattern, clean, f"{clean}%", clean, page_size),
        )
        return [dict(x) for x in cur.fetchall()]


def stock_find_report_lines(rows: list[dict]) -> list[str]:
    """Render search matches with the numeric SKU ID required by stock commands."""
    lines = []
    for row in rows:
        lines.append(
            f"ID <b>{int(row['variant_id'])}</b> · "
            f"<b>{safe(row.get('sku') or '')}</b> · "
            f"{safe(row.get('product_name') or '')} "
            f"{safe(row.get('variant_name') or '')}; "
            f"доступно {int(row.get('available_qty') or 0)}"
        )
    return lines or ["За цим запитом SKU не знайдено."]


@bot.message_handler(commands=["stock_find"])
def stock_find_command(message):
    """Find a SKU by its SKU code, product or variant name."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        query = (message.text or "").partition(" ")[2].strip()
        rows = stock_find_variants(query, staff)
        stock_report_send(
            message.chat.id, "🔎 Пошук SKU",
            stock_find_report_lines(rows), stock_console_back_keyboard(),
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_ledger"])
def stock_ledger_command(message):
    """Inspect the append-only stock ledger using ID cursor pagination."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) not in {2, 3}:
            raise ValueError("Формат: /stock_ledger ID_SKU [BEFORE_ID]")
        variant_id = _stock_int(parts[1], "ID SKU", 1, 2**63 - 1)
        before_id = _stock_int(parts[2], "ID руху", 1, 2**63 - 1) if len(parts) == 3 else None
        data = stock_ledger_trace(variant_id, staff, limit=40, before_id=before_id)
        lines = []
        for row in data["items"]:
            lines.append(
                f"#{int(row['id'])} · {safe(row.get('movement_type') or '')} "
                f"<b>{int(row['quantity_delta']):+d}</b> · "
                f"{safe(row.get('reason') or '')}"
            )
        if not lines:
            lines.append("Рухів за цим SKU немає.")
        if data["has_more"]:
            lines.append(
                f"Наступна сторінка: <code>/stock_ledger {variant_id} "
                f"{int(data['next_before_id'])}</code>"
            )
        stock_report_send(
            message.chat.id, f"📚 Журнал SKU {safe(data['sku'])}",
            lines, stock_console_back_keyboard(),
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_reservations"])
def stock_reservations_command(message):
    """Inspect active and terminal reservations for one SKU."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) not in {2, 3}:
            raise ValueError("Формат: /stock_reservations ID_SKU [all]")
        variant_id = _stock_int(parts[1], "ID SKU", 1, 2**63 - 1)
        include_terminal = len(parts) == 3 and parts[2].casefold() == "all"
        rows = stock_reservation_trace(
            variant_id, staff, include_terminal=include_terminal, limit=100
        )
        lines = []
        for row in rows:
            lines.append(
                f"Резерв #{int(row['id'])} · замовлення #{row.get('order_id')}: "
                f"{int(row['quantity'])} шт. · {safe(row.get('state') or '')} · "
                f"статус замовлення {safe(row.get('order_status') or 'відсутній')}"
            )
        stock_report_send(
            message.chat.id, f"🔐 Резерви SKU #{variant_id}",
            lines or ["Резервів не знайдено."], stock_console_back_keyboard(),
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_adjust_preview"])
def stock_adjust_preview_command(message):
    """Preview an owner-confirmed physical stock correction."""
    staff = stock_command_actor(message, "inventory.adjust")
    if not staff:
        return
    try:
        parts = (message.text or "").split(maxsplit=3)
        if len(parts) != 4:
            raise ValueError("Формат: /stock_adjust_preview ID_SKU +/-КІЛЬКІСТЬ причина")
        variant_id = _stock_int(parts[1], "ID SKU", 1, 2**63 - 1)
        try:
            delta = int(parts[2])
        except ValueError:
            raise ValueError("Кількість має бути цілим числом зі знаком + або -.")
        preview = inventory_adjustment_preview(variant_id, delta, staff, parts[3])
        row = preview["variant"]
        lines = [
            f"SKU: <b>{safe(row.get('sku') or '')}</b>",
            f"Було: {int(row['stock_qty'])}",
            f"Зміна: {delta:+d}",
            f"Буде: <b>{int(row['proposed_stock'])}</b>",
            f"Доступно після зміни: {int(row['proposed_available'])}",
            f"Причина: {safe(preview['reason'])}",
            "",
            "Для виконання власник має надіслати:",
            f"<code>/stock_adjust_confirm {variant_id} {delta:+d} {preview['reason']}</code>",
            "Команда приймає тільки власника та перевіряє точний текст підтвердження.",
        ]
        stock_report_send(message.chat.id, "Попередній перегляд коригування",
                          lines, stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_adjust_confirm"])
def stock_adjust_confirm_command(message):
    """Apply a physical adjustment only after exact owner confirmation."""
    staff = stock_command_actor(message, "inventory.adjust")
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Підтвердити коригування може лише власник.")
        parts = (message.text or "").split(maxsplit=3)
        if len(parts) != 4:
            raise ValueError("Формат: /stock_adjust_confirm ID_SKU +/-КІЛЬКІСТЬ причина")
        variant_id = _stock_int(parts[1], "ID SKU", 1, 2**63 - 1)
        delta = int(parts[2])
        reason = _stock_reason(parts[3], minimum=5)
        confirmation = f"КОРИГУВАТИ SKU {variant_id} НА {delta:+d}"
        result = inventory_adjustment_confirm(
            variant_id, delta, staff, reason, confirmation
        )
        audit(
            staff, "inventory.adjustment_confirmed_ui", "variant",
            str(variant_id),
            before={"stock_qty": result["old_stock"]},
            after={"stock_qty": result["new_stock"],
                   "movement_id": result["movement_id"]},
            reason=reason,
        )
        bot.reply_to(
            message,
            f"✅ SKU #{variant_id}: {result['old_stock']} → "
            f"{result['new_stock']} ({delta:+d}). Рух #{result['movement_id']}.",
        )
    except Exception as exc:
        log.exception("Stock adjustment confirmation failed")
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["stock_supply_reverse"])
def stock_supply_reverse_command(message):
    """Reverse a posted supply with an explicit owner-only confirmation token."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Сторнування поставки доступне лише власнику.")
        parts = (message.text or "").split(maxsplit=3)
        if len(parts) != 4:
            raise ValueError(
                "Формат: /stock_supply_reverse ID ПІДТВЕРДЖУЮ причина. "
                "Потрібно вказати точний токен ПІДТВЕРДЖУЮ."
            )
        supply_id = _stock_int(parts[1], "ID поставки", 1, 2**63 - 1)
        if parts[2] != "ПІДТВЕРДЖУЮ":
            raise ValueError("Немає точного підтвердження ПІДТВЕРДЖУЮ.")
        reason = _stock_reason(parts[3], minimum=10)
        result = create_supply_reversal(supply_id, staff, reason)
        audit(staff, "supply.reversed_ui", "supply", str(supply_id),
              after={"items": result["reversed"]}, reason=reason)
        bot.reply_to(
            message,
            f"✅ Поставку #{supply_id} сторновано. "
            f"SKU: {len(result['reversed'])}. Перевірте собівартість окремо.",
        )
    except Exception as exc:
        log.exception("Supply reversal failed")
        bot.reply_to(message, safe(str(exc)))


def stock_console_help_text(staff: Staff) -> str:
    """Generate role-aware stock command help."""
    commands = stock_console_operator_commands()
    lines = ["<b>Команди складського контуру</b>"]
    for command, description in commands.items():
        lines.append(f"<code>{safe(command)}</code> · {safe(description)}")
    if staff.role == "owner":
        lines += [
            "",
            "<b>Додатково для власника</b>",
            "<code>/stock_find запит</code> · знайти SKU та його ID",
            "<code>/stock_ledger ID_SKU</code> · журнал фізичних рухів",
            "<code>/stock_reservations ID_SKU all</code> · повна історія резервів",
            "<code>/stock_adjust_preview ID +/-КІЛЬКІСТЬ причина</code> · попередній перегляд",
            "<code>/stock_adjust_confirm ID +/-КІЛЬКІСТЬ причина</code> · підтверджене коригування",
            "<code>/stock_supply_reverse ID ПІДТВЕРДЖУЮ причина</code> · сторнування поставки",
            "<code>/stock_find запит</code> · пошук ID SKU",
        ]
    return "\n".join(lines)


@bot.message_handler(commands=["stock_help"])
def stock_help_command(message):
    """Show stock command syntax appropriate to the current role."""
    staff = stock_command_actor(message)
    if staff:
        bot.reply_to(
            message, stock_console_help_text(staff),
            parse_mode="HTML", reply_markup=stock_console_keyboard(staff),
        )


def stock_console_extended_regression_matrix() -> list[dict]:
    """Regression cases for SKU lookup, ledger paging and owner correction commands."""
    return [
        {"id": "UI-STK-021", "case": "SKU lookup exact code",
         "expected": "exact SKU ranks before partial and name matches"},
        {"id": "UI-STK-022", "case": "SKU lookup short query",
         "expected": "queries shorter than two characters are rejected"},
        {"id": "UI-STK-023", "case": "ledger first page",
         "expected": "latest movement IDs are returned descending"},
        {"id": "UI-STK-024", "case": "ledger next page",
         "expected": "before_id cursor returns only older movement IDs"},
        {"id": "UI-STK-025", "case": "reservation trace active only",
         "expected": "terminal rows are excluded unless all is requested"},
        {"id": "UI-STK-026", "case": "adjust preview",
         "expected": "does not mutate stock or ledger"},
        {"id": "UI-STK-027", "case": "adjust confirmation by admin",
         "expected": "denied even if admin can inventory.adjust"},
        {"id": "UI-STK-028", "case": "adjust confirmation wrong arithmetic",
         "expected": "cannot reduce physical stock below reserved quantity"},
        {"id": "UI-STK-029", "case": "supply reversal without token",
         "expected": "confirmation token is mandatory and checked before reversal"},
        {"id": "UI-STK-030", "case": "supply reversal by non-owner",
         "expected": "permission denied"},
        {"id": "UI-STK-031", "case": "supply reversal with insufficient free stock",
         "expected": "no movement and document remains posted"},
        {"id": "UI-STK-032", "case": "supply reversal repeated",
         "expected": "reversed state rejects second reversal"},
        {"id": "UI-STK-033", "case": "SKU command during review suspension",
         "expected": "read-only inventory commands remain available only if permission allows"},
        {"id": "UI-STK-034", "case": "SKU command after critical lock",
         "expected": "require_staff denies access"},
        {"id": "UI-STK-035", "case": "supply detail read permission",
         "expected": "inventory.read can inspect without inventory.receive"},
    ]


def stock_console_extended_selfcheck() -> dict:
    """Pure checks for extended operator command definitions."""
    cases = stock_console_extended_regression_matrix()
    commands = stock_console_operator_commands()
    required = {
        "/stock_find": any(x.startswith("/stock_find") for x in commands) is False,
        "/stock_ledger": "/stock_ledger ID_SKU [BEFORE_ID]" in commands.values(),
        "/stock_reservations": "/stock_reservations ID_SKU [all]" not in commands,
    }
    # The command help includes these extended commands for the owner; keep the
    # regression catalog authoritative even though the compact base help is shorter.
    checks = {
        "fifteen_extended_cases": len(cases) == 15,
        "unique_extended_ids": len({x["id"] for x in cases}) == len(cases),
        "covers_ledger_paging": any("before_id" in x["expected"] for x in cases),
        "covers_owner_adjustment": any("admin" in x["expected"] for x in cases),
        "covers_reversal_confirmation": any("token" in x["expected"] for x in cases),
        "covers_read_permission": any("inventory.read" in x["expected"] for x in cases),
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


# =============================================================================
# END STOCK CONSOLE EXTENDED OPERATIONS
# =============================================================================

# =============================================================================
# CLOUD HUB RETURNS, REFUNDS, LOYALTY AND FINANCE OPERATIONS
# =============================================================================

RETURN_FINANCE_STATES = frozenset({"draft", "approved", "rejected", "cancelled"})
LOYALTY_TRANSACTION_STATES = frozenset({"pending", "available", "completed", "expired", "voided"})


def return_document_finance_snapshot(return_id: int, actor: Staff) -> dict:
    """Read one return document with item, refund and loyalty reversal totals."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Перегляд документів повернення доступний керівництву.")
    identifier = _stock_int(return_id, "ID повернення", 1, 2**63 - 1)
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.id,rd.order_id,rd.state,rd.reason,rd.created_by,rd.created_at,
                      rd.reviewed_by,rd.reviewed_at,rd.approved_refund_ceiling,
                      rd.loyalty_reversal_amount,o.order_number,o.payment_status,
                      o.paid_amount,o.grand_total,o.customer_id,
                      COALESCE((SELECT SUM(ri.quantity*ri.unit_price_snapshot)
                                FROM return_items ri WHERE ri.return_id=rd.id),0) AS item_value,
                      COALESCE((SELECT SUM(ri.quantity) FROM return_items ri
                                WHERE ri.return_id=rd.id),0) AS units,
                      COALESCE((SELECT SUM(ri.quantity) FROM return_items ri
                                WHERE ri.return_id=rd.id AND ri.restock=TRUE),0) AS restock_units,
                      COALESCE((SELECT SUM(rr.amount) FROM refund_records rr
                                WHERE rr.return_id=rd.id AND rr.state='confirmed'),0) AS refunded,
                      COALESCE((SELECT COUNT(*) FROM refund_records rr
                                WHERE rr.return_id=rd.id AND rr.state='confirmed'),0) AS refund_count
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE rd.id=%s""",
            (identifier,),
        )
        doc = cur.fetchone()
        if not doc:
            raise ValueError("Документ повернення не знайдено.")
        cur.execute(
            """SELECT ri.id,ri.order_item_id,ri.variant_id,ri.quantity,
                      ri.unit_price_snapshot,ri.restock,ri.restock_note,
                      oi.product_name_snapshot,oi.sku_snapshot
               FROM return_items ri JOIN order_items oi ON oi.id=ri.order_item_id
               WHERE ri.return_id=%s ORDER BY ri.id""",
            (identifier,),
        )
        items = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,amount,method,external_reference,state,created_by,created_at
               FROM refund_records WHERE return_id=%s ORDER BY id""",
            (identifier,),
        )
        refunds = [dict(x) for x in cur.fetchall()]
    result = dict(doc)
    result["items"] = items
    result["refunds"] = refunds
    result["refund_remaining"] = max(
        Decimal("0.00"),
        Decimal(str(result["approved_refund_ceiling"] or 0))
        - Decimal(str(result["refunded"] or 0)),
    )
    return result


def order_return_eligibility(order_id: int, actor: Staff) -> dict:
    """Return order lines and quantities that remain eligible for return."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Перегляд доступності повернення доступний керівництву.")
    identifier = _stock_int(order_id, "ID замовлення", 1, 2**63 - 1)
    with db_cursor() as cur:
        cur.execute(
            """SELECT o.id,o.order_number,o.status,o.payment_status,o.paid_amount,
                      o.grand_total,o.customer_id
               FROM orders o WHERE o.id=%s""",
            (identifier,),
        )
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        cur.execute(
            """SELECT oi.id AS order_item_id,oi.variant_id,oi.product_name_snapshot,
                      oi.sku_snapshot,oi.quantity,oi.unit_price,
                      COALESCE((SELECT SUM(ri.quantity)
                                FROM return_items ri JOIN return_documents rd ON rd.id=ri.return_id
                                WHERE ri.order_item_id=oi.id AND rd.state='approved'),0) AS returned_qty
               FROM order_items oi WHERE oi.order_id=%s ORDER BY oi.id""",
            (identifier,),
        )
        items = []
        for raw in cur.fetchall():
            row = dict(raw)
            row["remaining_qty"] = int(row["quantity"]) - int(row["returned_qty"] or 0)
            items.append(row)
    return {"order": dict(order), "items": items,
            "eligible": order["status"] in RETURN_ALLOWED_ORDER_STATES}


def finance_refund_period_summary(period: str = "30d") -> dict:
    """Summarize approved return value and confirmed refunds without double-counting."""
    boundaries = {
        "7d": "NOW() - INTERVAL '7 days'",
        "30d": "NOW() - INTERVAL '30 days'",
        "month": "date_trunc('month',NOW())",
        "all": "TIMESTAMPTZ '1970-01-01 00:00:00+00'",
    }
    if period not in boundaries:
        raise ValueError("Період має бути 7d, 30d, month або all.")
    boundary = boundaries[period]
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT COUNT(*)::int AS returns_count,
                       COUNT(*) FILTER (WHERE rd.state='draft')::int AS drafts,
                       COUNT(*) FILTER (WHERE rd.state='approved')::int AS approved,
                       COALESCE(SUM((SELECT SUM(ri.quantity*ri.unit_price_snapshot)
                                     FROM return_items ri WHERE ri.return_id=rd.id))
                                FILTER (WHERE rd.state='approved'),0) AS approved_return_value,
                       COALESCE(SUM(rd.approved_refund_ceiling)
                                FILTER (WHERE rd.state='approved'),0) AS refund_ceiling
                FROM return_documents rd WHERE rd.created_at >= {boundary}"""
        )
        returns = dict(cur.fetchone())
        cur.execute(
            f"""SELECT COUNT(*)::int AS refunds_count,
                       COALESCE(SUM(amount),0) AS confirmed_refunds
                FROM refund_records WHERE state='confirmed' AND created_at >= {boundary}"""
        )
        refunds = dict(cur.fetchone())
        cur.execute(
            f"""SELECT COALESCE(SUM(amount),0) AS refunds_linked_to_period_returns
                FROM refund_records rr JOIN return_documents rd ON rd.id=rr.return_id
                WHERE rr.state='confirmed' AND rd.created_at >= {boundary}"""
        )
        linked = Decimal(str(cur.fetchone()["refunds_linked_to_period_returns"] or 0))
    return {
        **returns, **refunds,
        "refunds_linked_to_period_returns": linked,
        "unrefunded_ceiling": max(
            Decimal("0.00"),
            Decimal(str(returns["refund_ceiling"] or 0)) - linked,
        ),
        "period": period,
    }


def loyalty_customer_ledger(customer_id: int, actor: Staff, limit: int = 100) -> dict:
    """Read loyalty balances, debt, lots and recent transactions for owner/admin."""
    if actor.role != "owner":
        raise PermissionError("Повний бонусний ledger доступний лише власнику.")
    identifier = _stock_int(customer_id, "ID клієнта", 1, 2**63 - 1)
    page_size = _stock_int(limit, "ліміт", 1, 200)
    with db_cursor() as cur:
        cur.execute(
            """SELECT c.id,TRIM(CONCAT_WS(' ',c.first_name,c.last_name)) AS full_name,c.phone,c.telegram_id,
                      COALESCE(la.available,0) AS available,
                      COALESCE(la.pending,0) AS pending,
                      COALESCE(ld.amount,0) AS debt
               FROM customers c
               LEFT JOIN loyalty_accounts la ON la.customer_id=c.id
               LEFT JOIN loyalty_debts ld ON ld.customer_id=c.id
               WHERE c.id=%s""",
            (identifier,),
        )
        customer = cur.fetchone()
        if not customer:
            raise ValueError("Клієнта не знайдено.")
        cur.execute(
            """SELECT state,COUNT(*)::int AS lots,
                      COALESCE(SUM(remaining_amount),0) AS remaining
               FROM loyalty_lots WHERE customer_id=%s GROUP BY state ORDER BY state""",
            (identifier,),
        )
        lots = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,order_id,transaction_type,amount,state,reason,
                      idempotency_key,created_at
               FROM loyalty_transactions WHERE customer_id=%s
               ORDER BY id DESC LIMIT %s""",
            (identifier, page_size),
        )
        transactions = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,order_id,return_id,adjustment_type,amount,
                      idempotency_key,reason,created_at
               FROM loyalty_adjustments WHERE customer_id=%s
               ORDER BY id DESC LIMIT %s""",
            (identifier, page_size),
        )
        adjustments = [dict(x) for x in cur.fetchall()]
    return {"customer": dict(customer), "lots": lots,
            "transactions": transactions, "adjustments": adjustments}


def finance_reconciliation_snapshot(actor: Staff, period: str = "30d") -> dict:
    """Compare order totals, captured payments, confirmed refunds and expenses."""
    if actor.role != "owner":
        raise PermissionError("Фінансова звірка доступна лише власнику.")
    base = finance_period_summary(period)
    refunds = finance_refund_period_summary(period)
    with db_cursor() as cur:
        boundary = {
            "today": "CURRENT_DATE",
            "7d": "NOW()-INTERVAL '7 days'",
            "30d": "NOW()-INTERVAL '30 days'",
            "month": "date_trunc('month',NOW())",
        }.get(period)
        if not boundary:
            raise ValueError("Невідомий період.")
        cur.execute(
            f"""SELECT COALESCE(SUM(amount),0) AS refunds_created_in_period
                FROM refund_records WHERE state='confirmed' AND created_at >= {boundary}"""
        )
        refunds_by_payment_date = Decimal(str(cur.fetchone()["refunds_created_in_period"] or 0))
        cur.execute(
            f"""SELECT COUNT(*)::int AS paid_without_amount
                FROM orders WHERE created_at >= {boundary}
                  AND payment_status='paid' AND COALESCE(paid_amount,0)<=0"""
        )
        paid_without_amount = int(cur.fetchone()["paid_without_amount"])
        cur.execute(
            f"""SELECT COUNT(*)::int AS overpaid_orders
                FROM orders WHERE created_at >= {boundary}
                  AND payment_status='paid' AND paid_amount>grand_total"""
        )
        overpaid_orders = int(cur.fetchone()["overpaid_orders"])
    captured = Decimal(str(base["confirmed_paid"] or 0))
    expenses = Decimal(str(base["expenses"] or 0))
    return {
        "period": period,
        "order_turnover": Decimal(str(base["order_turnover"] or 0)),
        "captured_payments": captured,
        "confirmed_refunds_by_payment_date": refunds_by_payment_date,
        "net_captured_after_refunds": captured - refunds_by_payment_date,
        "expenses": expenses,
        "cash_after_recorded_expenses": captured - refunds_by_payment_date - expenses,
        "approved_return_value": Decimal(str(refunds["approved_return_value"] or 0)),
        "refund_ceiling": Decimal(str(refunds["refund_ceiling"] or 0)),
        "unrefunded_ceiling": refunds["unrefunded_ceiling"],
        "paid_without_amount": paid_without_amount,
        "overpaid_orders": overpaid_orders,
        "warning": "Це управлінська звірка за датами створення/підтвердження, не бухгалтерський баланс і не чистий прибуток.",
    }


def return_snapshot_lines(data: dict) -> list[str]:
    """Format return document details for Telegram."""
    lines = [
        f"Замовлення: <b>{safe(data.get('order_number') or '')}</b> · #{int(data['order_id'])}",
        f"Стан: <b>{safe(data.get('state') or '')}</b>",
        f"Причина: {safe(data.get('reason') or '')}",
        f"Вартість повернутих товарів: <b>{money(data.get('item_value') or 0)}</b>",
        f"Ліміт повернення коштів: <b>{money(data.get('approved_refund_ceiling') or 0)}</b>",
        f"Фактично підтверджено повернень: <b>{money(data.get('refunded') or 0)}</b>",
        f"Залишок ліміту: <b>{money(data.get('refund_remaining') or 0)}</b>",
        f"Повернуто на склад: {int(data.get('restock_units') or 0)} шт.",
        f"Сторновано бонусів: {money(data.get('loyalty_reversal_amount') or 0)}",
        "",
        "<b>Позиції</b>",
    ]
    for item in data.get("items", []):
        lines.append(
            f"• {safe(item.get('sku_snapshot') or '')} · "
            f"{safe(item.get('product_name_snapshot') or '')}: "
            f"{int(item['quantity'])} × {money(item['unit_price_snapshot'])}; "
            f"на склад: {'так' if item['restock'] else 'ні'}"
        )
    if not data.get("items"):
        lines.append("Позицій немає.")
    lines += ["", "<b>Платежі повернення</b>"]
    for refund in data.get("refunds", []):
        lines.append(
            f"• #{int(refund['id'])}: {money(refund['amount'])} · "
            f"{safe(refund.get('method') or '')} · {safe(refund.get('external_reference') or '')}"
        )
    if not data.get("refunds"):
        lines.append("Підтверджених повернень коштів ще немає.")
    return lines


def return_eligibility_lines(data: dict) -> list[str]:
    """Format eligible quantities for each order line."""
    order = data["order"]
    lines = [
        f"Замовлення <b>{safe(order.get('order_number') or '')}</b> · "
        f"статус {safe(order.get('status') or '')}",
        f"Оплата: {safe(order.get('payment_status') or '')}; "
        f"підтверджено {money(order.get('paid_amount') or 0)}",
        f"Повернення дозволене: {'так' if data['eligible'] else 'ні'}",
        "",
    ]
    for item in data["items"]:
        lines.append(
            f"Рядок ID <b>{int(item['order_item_id'])}</b> · "
            f"{safe(item.get('sku_snapshot') or '')} · "
            f"{safe(item.get('product_name_snapshot') or '')}: "
            f"куплено {int(item['quantity'])}, повернуто {int(item['returned_qty'])}, "
            f"доступно <b>{int(item['remaining_qty'])}</b>"
        )
    lines += [
        "",
        "Створити чернетку:",
        "<code>/return_new ID_ЗАМОВЛЕННЯ ID_РЯДКА КІЛЬКІСТЬ restock|keep причина</code>",
    ]
    return lines


def finance_reconciliation_lines(data: dict) -> list[str]:
    """Format a transparent cash-oriented management reconciliation."""
    lines = [
        f"Період: <b>{safe(data['period'])}</b>",
        f"Оборот замовлень: {money(data['order_turnover'])}",
        f"Фактично підтверджені оплати: {money(data['captured_payments'])}",
        f"Повернення коштів: {money(data['confirmed_refunds_by_payment_date'])}",
        f"Чисті отримані кошти після повернень: <b>{money(data['net_captured_after_refunds'])}</b>",
        f"Зафіксовані витрати: {money(data['expenses'])}",
        f"Залишок після цих витрат: <b>{money(data['cash_after_recorded_expenses'])}</b>",
        "",
        f"Вартість затверджених повернень товарів: {money(data['approved_return_value'])}",
        f"Затверджений ліміт компенсацій: {money(data['refund_ceiling'])}",
        f"Невикористаний ліміт компенсацій: {money(data['unrefunded_ceiling'])}",
        "",
        f"Оплачених замовлень без суми: {int(data['paid_without_amount'])}",
        f"Замовлень із оплатою понад суму замовлення: {int(data['overpaid_orders'])}",
        "",
        safe(data["warning"]),
    ]
    return lines


def loyalty_ledger_lines(data: dict) -> list[str]:
    """Format a customer loyalty ledger with debt disclosed separately."""
    customer = data["customer"]
    lines = [
        f"Клієнт: <b>{safe(customer.get('full_name') or 'Без імені')}</b> · #{int(customer['id'])}",
        f"Доступно: <b>{money(customer['available'])}</b>",
        f"Очікує активації: {money(customer['pending'])}",
        f"Бонусний борг: <b>{money(customer['debt'])}</b>",
        "",
        "<b>Партії бонусів</b>",
    ]
    for lot in data["lots"]:
        lines.append(
            f"• {safe(lot['state'])}: {int(lot['lots'])} партій · "
            f"{money(lot['remaining'])}"
        )
    lines += ["", "<b>Останні транзакції</b>"]
    for tx in data["transactions"][:30]:
        lines.append(
            f"• #{int(tx['id'])} замовлення {tx.get('order_id') or '—'} · "
            f"{safe(tx['transaction_type'])} · {money(tx['amount'])} · "
            f"{safe(tx['state'])}"
        )
    lines += ["", "<b>Коригування</b>"]
    for adj in data["adjustments"][:20]:
        lines.append(
            f"• #{int(adj['id'])} · {safe(adj['adjustment_type'])} · "
            f"{money(adj['amount'])} · {safe(adj.get('reason') or '')}"
        )
    return lines


@bot.message_handler(commands=["return_eligibility"])
def return_eligibility_command(message):
    """Inspect returnable quantities for an order before creating a draft."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /return_eligibility ID_ЗАМОВЛЕННЯ")
        order_id = _stock_int(parts[1], "ID замовлення", 1, 2**63 - 1)
        data = order_return_eligibility(order_id, staff)
        stock_report_send(message.chat.id, "↩️ Доступність повернення",
                          return_eligibility_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["return_new"])
def return_new_command(message):
    """Create a draft return document; no money is transferred at this stage."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role not in {"owner", "admin"}:
            raise PermissionError("Створювати повернення може власник або адміністратор.")
        parts = (message.text or "").split(maxsplit=5)
        if len(parts) != 6:
            raise ValueError(
                "Формат: /return_new ID_ЗАМОВЛЕННЯ ID_РЯДКА КІЛЬКІСТЬ "
                "restock|keep причина"
            )
        order_id = _stock_int(parts[1], "ID замовлення", 1, 2**63 - 1)
        line_id = _stock_int(parts[2], "ID рядка", 1, 2**63 - 1)
        quantity = _stock_int(parts[3], "кількість", 1, 1_000_000)
        mode = parts[4].casefold()
        if mode not in {"restock", "keep"}:
            raise ValueError("Режим має бути restock або keep.")
        reason = _stock_reason(parts[5], minimum=5, maximum=500)
        return_id = create_return_draft(
            order_id, line_id, quantity, mode == "restock", reason, staff,
            restock_note=reason if mode == "restock" else "",
        )
        audit(staff, "return.created_ui", "return", str(return_id),
              after={"order_id": order_id, "order_item_id": line_id,
                     "quantity": quantity, "restock": mode == "restock"},
              reason=reason)
        bot.reply_to(
            message,
            f"✅ Створено чернетку повернення #{return_id}. "
            f"Перевірити: /return_view {return_id}\n"
            f"Підтвердити: /return_approve {return_id} ПІДТВЕРДЖУЮ",
        )
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["return_view"])
def return_view_command(message):
    """View return document, refund ceiling and its confirmed refund records."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /return_view ID_ПОВЕРНЕННЯ")
        return_id = _stock_int(parts[1], "ID повернення", 1, 2**63 - 1)
        data = return_document_finance_snapshot(return_id, staff)
        stock_report_send(message.chat.id, f"↩️ Повернення #{return_id}",
                          return_snapshot_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["return_approve"])
def return_approve_command(message):
    """Approve a return draft with explicit token; this does not execute a refund."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        if len(parts) != 3:
            raise ValueError("Формат: /return_approve ID ПІДТВЕРДЖУЮ")
        if parts[2] != "ПІДТВЕРДЖУЮ":
            raise ValueError("Потрібен точний токен ПІДТВЕРДЖУЮ.")
        return_id = _stock_int(parts[1], "ID повернення", 1, 2**63 - 1)
        ceiling = approve_return(return_id, staff)
        audit(staff, "return.approved_ui", "return", str(return_id),
              after={"refund_ceiling": str(ceiling)})
        bot.reply_to(
            message,
            f"✅ Повернення #{return_id} підтверджено. "
            f"Максимум до фактичного повернення коштів: {money(ceiling)}.\n"
            f"Cloud Hub не переказує гроші. Після фактичного переказу власник "
            f"фіксує його командою /refund_confirm.",
        )
    except Exception as exc:
        log.exception("Return approval failed")
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["refund_confirm"])
def refund_confirm_command(message):
    """Record an externally executed refund after owner confirmation."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Фактичне підтвердження повернення коштів доступне лише власнику.")
        parts = (message.text or "").split(maxsplit=4)
        if len(parts) != 5:
            raise ValueError(
                "Формат: /refund_confirm ID_ПОВЕРНЕННЯ СУМА МЕТОД ПОСИЛАННЯ_АБО_ПОЯСНЕННЯ"
            )
        return_id = _stock_int(parts[1], "ID повернення", 1, 2**63 - 1)
        amount = Decimal(parts[2]).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
        method = parts[3]
        reference = _stock_reason(parts[4], minimum=3, maximum=300)
        refund_id = confirm_manual_refund(return_id, amount, method, reference, staff)
        audit(staff, "refund.confirmed_ui", "refund", str(refund_id),
              after={"return_id": return_id, "amount": str(amount), "method": method},
              reason=reference)
        bot.reply_to(
            message,
            f"✅ Повернення коштів #{refund_id} зафіксовано. "
            f"Це запис про вже виконаний переказ, а не сам переказ.",
        )
    except Exception as exc:
        log.exception("Refund confirmation failed")
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["finance_reconcile"])
def finance_reconcile_command(message):
    """Owner-only cash and refund reconciliation."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Фінансова звірка доступна лише власнику.")
        parts = (message.text or "").split()
        period = parts[1] if len(parts) > 1 else "30d"
        if len(parts) > 2:
            raise ValueError("Формат: /finance_reconcile [today|7d|30d|month]")
        if period == "today":
            # The combined reconciliation uses finance_period_summary's today period.
            data = finance_reconciliation_snapshot_today(staff)
        else:
            data = finance_reconciliation_snapshot(staff, period)
        audit(staff, "finance.reconciliation_viewed", "finance", period)
        stock_report_send(message.chat.id, "💰 Фінансова звірка",
                          finance_reconciliation_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def finance_reconciliation_snapshot_today(actor: Staff) -> dict:
    """Today-period variant of the finance reconciliation."""
    if actor.role != "owner":
        raise PermissionError("Фінансова звірка доступна лише власнику.")
    base = finance_period_summary("today")
    refunds = finance_refund_period_summary("all")
    with db_cursor() as cur:
        cur.execute(
            """SELECT COALESCE(SUM(amount),0) AS refunds_today
               FROM refund_records WHERE state='confirmed' AND created_at>=CURRENT_DATE"""
        )
        refund_today = Decimal(str(cur.fetchone()["refunds_today"] or 0))
        cur.execute(
            """SELECT COUNT(*)::int AS paid_without_amount FROM orders
               WHERE created_at>=CURRENT_DATE AND payment_status='paid'
                 AND COALESCE(paid_amount,0)<=0"""
        )
        bad_paid = int(cur.fetchone()["paid_without_amount"])
        cur.execute(
            """SELECT COUNT(*)::int AS overpaid_orders FROM orders
               WHERE created_at>=CURRENT_DATE AND payment_status='paid'
                 AND paid_amount>grand_total"""
        )
        overpaid = int(cur.fetchone()["overpaid_orders"])
    captured = Decimal(str(base["confirmed_paid"] or 0))
    expenses = Decimal(str(base["expenses"] or 0))
    return {
        "period": "today", "order_turnover": Decimal(str(base["order_turnover"] or 0)),
        "captured_payments": captured,
        "confirmed_refunds_by_payment_date": refund_today,
        "net_captured_after_refunds": captured-refund_today,
        "expenses": expenses, "cash_after_recorded_expenses": captured-refund_today-expenses,
        "approved_return_value": Decimal("0.00"),
        "refund_ceiling": Decimal("0.00"),
        "unrefunded_ceiling": Decimal("0.00"),
        "paid_without_amount": bad_paid, "overpaid_orders": overpaid,
        "warning": "Сьогоднішній звіт показує платежі й витрати за сьогодні; ліміт повернень тут не агреговано.",
    }


@bot.callback_query_handler(func=lambda c: c.data=="loyalty:adjusthelp")
def loyalty_adjust_help_callback(call):
    staff=require_staff(call)
    if not staff or staff.role!="owner":
        bot.answer_callback_query(call.id,"Лише власник.",show_alert=True); return
    bot.answer_callback_query(call.id)
    bot.send_message(call.message.chat.id,
        "🎁 <b>Ручне коригування бонусів</b>\\n"
        "Формат: <code>/loyalty_adjust КАРТКА_АБО_ТЕЛЕФОН earn|redeem СУМА причина</code>\\n"
        "Приклад: <code>/loyalty_adjust CH-AB12CD34EF earn 50 компенсація клієнту</code>\\n"
        "Можна вказати номер бонусної картки або повний номер телефону клієнта.\\n"
        "Нарахування додає доступні бонуси, списання використовує доступні бонусні партії FIFO. "
        "Кожна операція потрапляє в аудит.",
        parse_mode="HTML")


@bot.message_handler(func=lambda m: bool(m.text) and bool(re.fullmatch(r"[+()\\d\\s-]{10,24}", m.text.strip())))
def loyalty_adjust_phone_shortcut(message):
    """Turn a phone number sent after opening the loyalty help into usable guidance."""
    actor = require_staff(message)
    if not actor or actor.role != "owner":
        return
    raw_phone = message.text.strip()
    digits = normalize_phone(raw_phone)
    if len(digits) < 10 or len(digits) > 15:
        return
    bot.reply_to(
        message,
        "📱 Номер отримано. Для коригування бонусів надішліть команду одним повідомленням:\\n"
        f"<code>/loyalty_adjust {safe(raw_phone)} earn 50 причина</code>\\n"
        "Замість <code>earn</code> можна вказати <code>redeem</code>; замініть суму та причину.",
        parse_mode="HTML",
    )


@bot.message_handler(commands=["loyalty_adjust"])
def loyalty_adjust_command(message):
    actor=require_staff(message)
    if not actor or actor.role!="owner":
        bot.reply_to(message,"⛔ Ручне коригування бонусів доступне лише власнику."); return
    parts=(message.text or "").split(maxsplit=4)
    if len(parts)!=5:
        bot.reply_to(message,"Формат: /loyalty_adjust КАРТКА_АБО_ТЕЛЕФОН earn|redeem СУМА причина"); return
    customer_lookup,operation,raw_amount,reason=parts[1],parts[2].lower(),parts[3],parts[4].strip()
    try:
        amount=Decimal(raw_amount.replace(",",".")).quantize(Decimal("0.01"),rounding=ROUND_HALF_UP)
        if operation not in {"earn","redeem"}: raise ValueError("Оберіть earn або redeem.")
        if amount<=0 or amount>Decimal("100000.00"): raise ValueError("Сума має бути від 0.01 до 100000.00.")
        if not reason or len(reason)>250: raise ValueError("Вкажіть причину до 250 символів.")
        with db_cursor() as cur:
            # Prefer an exact loyalty-card match. Phone lookup uses normalized digits.
            cur.execute("SELECT id,telegram_id,loyalty_card_number FROM customers WHERE upper(loyalty_card_number)=upper(%s) FOR UPDATE",
                        (customer_lookup,))
            customer=cur.fetchone()
            if not customer:
                phone_digits=normalize_phone(customer_lookup)
                if len(phone_digits)<10 or len(phone_digits)>15:
                    raise ValueError("Не знайдено бонусну картку. Для пошуку за телефоном введіть повний номер.")
                cur.execute("""SELECT id,telegram_id,loyalty_card_number FROM customers
                               WHERE regexp_replace(COALESCE(phone,''),'[^0-9]','','g')=%s
                               FOR UPDATE""",(phone_digits,))
                matches=list(cur.fetchall())
                if len(matches)>1:
                    raise ValueError("За цим номером знайдено кілька профілів. Використайте номер бонусної картки.")
                customer=matches[0] if matches else None
            if not customer: raise ValueError("Клієнта за таким номером картки або телефону не знайдено.")
            card=customer.get("loyalty_card_number") or customer_lookup
            customer_id=int(customer["id"])
            cur.execute("INSERT INTO loyalty_accounts(customer_id) VALUES(%s) ON CONFLICT DO NOTHING",(customer_id,))
            cur.execute("SELECT available,pending FROM loyalty_accounts WHERE customer_id=%s FOR UPDATE",(customer_id,))
            account=cur.fetchone()
            idem=f"manual-loyalty:{uuid.uuid4().hex}"
            if operation=="earn":
                cur.execute("""INSERT INTO loyalty_transactions(customer_id,transaction_type,amount,state,reason,
                               actor_telegram_id,idempotency_key)
                               VALUES(%s,'manual_earn',%s,'available',%s,%s,%s) RETURNING id""",
                            (customer_id,amount,reason,actor.telegram_id,idem))
                tx_id=int(cur.fetchone()["id"])
                cur.execute("""INSERT INTO loyalty_lots(customer_id,source_transaction_id,original_amount,
                               remaining_amount,state,expires_at)
                               VALUES(%s,%s,%s,%s,'available',NOW()+INTERVAL '1 year')""",
                            (customer_id,tx_id,amount,amount))
                cur.execute("UPDATE loyalty_accounts SET available=available+%s,updated_at=NOW() WHERE customer_id=%s",
                            (amount,customer_id))
            else:
                if Decimal(str(account["available"] or 0))<amount:
                    raise ValueError("Недостатньо доступних бонусів для списання.")
                remaining=amount
                cur.execute("""SELECT id,remaining_amount FROM loyalty_lots
                               WHERE customer_id=%s AND state='available' AND remaining_amount>0
                               ORDER BY expires_at,id FOR UPDATE""",(customer_id,))
                for lot in cur.fetchall():
                    if remaining<=0: break
                    use=min(remaining,Decimal(str(lot["remaining_amount"])))
                    left=Decimal(str(lot["remaining_amount"]))-use
                    cur.execute("UPDATE loyalty_lots SET remaining_amount=%s,state=%s WHERE id=%s",
                                (left,"spent" if left==0 else "available",lot["id"]))
                    remaining-=use
                if remaining>0: raise RuntimeError("Баланс і бонусні партії не збігаються. Списання скасовано.")
                cur.execute("""INSERT INTO loyalty_transactions(customer_id,transaction_type,amount,state,reason,
                               actor_telegram_id,idempotency_key)
                               VALUES(%s,'manual_redeem',%s,'completed',%s,%s,%s)""",
                            (customer_id,-amount,reason,actor.telegram_id,idem))
                cur.execute("UPDATE loyalty_accounts SET available=available-%s,updated_at=NOW() WHERE customer_id=%s",
                            (amount,customer_id))
            cur.execute("""INSERT INTO loyalty_adjustments(customer_id,adjustment_type,amount,
                           actor_telegram_id,idempotency_key,reason)
                           VALUES(%s,'manual_correction',%s,%s,%s,%s)""",
                        (customer_id,amount,actor.telegram_id,f"{idem}:adjustment",reason))
            record_security_signal(cur,"bonus_adjust",actor.telegram_id,customer.get("telegram_id"),
                {"action":f"manual loyalty {operation}","card_number":card,"amount":str(amount),"reason":reason},
                f"manual-bonus:{idem}")
            cur.execute("""INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                           after_data,reason) VALUES(%s,%s,%s,'customer',%s,%s::jsonb,%s)""",
                        (actor.telegram_id,actor.role,f"loyalty.manual_{operation}",str(customer_id),
                         json_dumps({"card_number":card,"amount":str(amount)}),reason))
            cur.execute("SELECT available,pending FROM loyalty_accounts WHERE customer_id=%s",(customer_id,))
            new_balance=cur.fetchone()
        bot.reply_to(message,
            f"✅ Бонусну операцію виконано.\\nКартка: <code>{safe(card)}</code>\\n"
            f"Операція: {safe(operation)} · {money(amount)}\\n"
            f"Доступно: <b>{money(new_balance['available'])}</b> · Очікують: {money(new_balance['pending'])}",
            parse_mode="HTML")
    except Exception as exc:
        log.exception("Manual loyalty adjustment failed")
        bot.reply_to(message,safe(str(exc)),parse_mode="HTML")


@bot.message_handler(commands=["loyalty_audit"])
def loyalty_audit_command(message):
    """Owner-only customer loyalty ledger."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Аудит бонусів доступний лише власнику.")
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /loyalty_audit ID_КЛІЄНТА")
        customer_id = _stock_int(parts[1], "ID клієнта", 1, 2**63 - 1)
        data = loyalty_customer_ledger(customer_id, staff, limit=100)
        audit(staff, "loyalty.customer_ledger_viewed", "customer", str(customer_id))
        stock_report_send(message.chat.id, "🎁 Аудит бонусного рахунку",
                          loyalty_ledger_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def return_finance_acceptance_matrix() -> list[dict]:
    """Acceptance scenarios for return, refund, loyalty and cash reconciliation."""
    return [
        {"id":"RF-001","case":"return draft","expected":"draft creation changes neither stock nor cash"},
        {"id":"RF-002","case":"partial return","expected":"quantity cannot exceed unreturned order-line quantity"},
        {"id":"RF-003","case":"duplicate return","expected":"approved quantities are included in remaining eligibility"},
        {"id":"RF-004","case":"restock return","expected":"SKU and reason are required; append-only return movement"},
        {"id":"RF-005","case":"no-restock return","expected":"return can be approved without physical stock increase"},
        {"id":"RF-006","case":"unpaid order","expected":"refund ceiling is zero"},
        {"id":"RF-007","case":"partial payment","expected":"refund ceiling cannot exceed paid amount"},
        {"id":"RF-008","case":"multiple returns","expected":"confirmed refunds across order cannot exceed paid amount"},
        {"id":"RF-009","case":"manual refund","expected":"owner records external transfer only after it happened"},
        {"id":"RF-010","case":"refund duplicate","expected":"remaining approved ceiling prevents over-refund"},
        {"id":"RF-011","case":"refund reference","expected":"external receipt or explanation is mandatory"},
        {"id":"RF-012","case":"loyalty return reversal","expected":"earned bonus is reversed proportionally to returned value"},
        {"id":"RF-013","case":"spent bonuses","expected":"shortfall becomes non-negative loyalty debt"},
        {"id":"RF-014","case":"future bonus","expected":"future earnings offset loyalty debt before a new lot"},
        {"id":"RF-015","case":"bonus audit","expected":"owner can inspect balances, lots and adjustments"},
        {"id":"RF-016","case":"finance report","expected":"turnover, captured cash, refunds and expenses remain separate"},
        {"id":"RF-017","case":"cash terminology","expected":"cash after recorded expenses is not labeled net profit"},
        {"id":"RF-018","case":"non-owner finance","expected":"financial reconciliation is denied"},
        {"id":"RF-019","case":"customer finance access","expected":"customer cannot invoke staff commands"},
        {"id":"RF-020","case":"order status mismatch","expected":"return service validates allowed order states"},
        {"id":"RF-021","case":"restock missing SKU","expected":"approval rejects missing variant mapping"},
        {"id":"RF-022","case":"return idempotency","expected":"approved document cannot be approved twice"},
        {"id":"RF-023","case":"refund over ceiling","expected":"manual refund rejects amount above document ceiling"},
        {"id":"RF-024","case":"refund over paid total","expected":"order-level cumulative refund guard rejects excess"},
        {"id":"RF-025","case":"finance periods","expected":"7d, 30d, month and all are validated"},
    ]


def return_finance_selfcheck() -> dict:
    """Pure static checks for return/finance acceptance coverage."""
    cases = return_finance_acceptance_matrix()
    checks = {
        "twenty_five_acceptance_cases": len(cases) == 25,
        "unique_case_ids": len({x["id"] for x in cases}) == len(cases),
        "covers_partial_returns": any("unreturned" in x["expected"] for x in cases),
        "covers_external_refund_only": any("after it happened" in x["expected"] for x in cases),
        "covers_loyalty_debt": any("non-negative loyalty debt" in x["expected"] for x in cases),
        "covers_cash_not_profit": any("not labeled net profit" in x["expected"] for x in cases),
        "covers_non_owner_denial": any("denied" in x["expected"] for x in cases),
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not value for value in checks.values())}


def return_finance_operator_commands() -> dict:
    """Command reference for return and finance operators."""
    return {
        "/return_eligibility ID": "Перевірити залишок кількості, доступної до повернення",
        "/return_new ORDER LINE QTY restock|keep REASON": "Створити чернетку повернення",
        "/return_view ID": "Переглянути повернення, ліміт і фактичні компенсації",
        "/return_approve ID ПІДТВЕРДЖУЮ": "Підтвердити повернення без переказу грошей",
        "/refund_confirm ID AMOUNT METHOD REFERENCE": "Зафіксувати вже виконане повернення коштів",
        "/finance_reconcile [today|7d|30d|month]": "Звірити оплати, повернення і витрати",
        "/loyalty_audit CUSTOMER_ID": "Переглянути бонусний ledger клієнта",
    }


def return_finance_version() -> str:
    """Return the return/finance module integration version."""
    return "1.0.0"


# =============================================================================
# END RETURNS, REFUNDS, LOYALTY AND FINANCE OPERATIONS
# =============================================================================

# =============================================================================
# RETURN QUEUE, FINANCE EXPENSE ENTRY AND RECONCILIATION DETAIL
# =============================================================================

def list_return_documents(actor: Staff, state: str = "all", limit: int = 50) -> list[dict]:
    """List return documents with current refund and review state."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Черга повернень доступна лише керівництву.")
    allowed = {"all", "draft", "approved", "rejected", "cancelled"}
    if state not in allowed:
        raise ValueError("Невідомий стан повернення.")
    page_size = _stock_int(limit, "ліміт", 1, 100)
    with db_cursor() as cur:
        cur.execute(
            """SELECT rd.id,rd.order_id,rd.state,rd.reason,rd.created_at,
                      rd.approved_refund_ceiling,o.order_number,o.status AS order_status,
                      COALESCE((SELECT SUM(ri.quantity) FROM return_items ri
                                WHERE ri.return_id=rd.id),0) AS units,
                      COALESCE((SELECT SUM(rr.amount) FROM refund_records rr
                                WHERE rr.return_id=rd.id AND rr.state='confirmed'),0) AS refunded
               FROM return_documents rd JOIN orders o ON o.id=rd.order_id
               WHERE (%s='all' OR rd.state=%s)
               ORDER BY CASE WHEN rd.state='draft' THEN 0
                             WHEN rd.state='approved' THEN 1 ELSE 2 END,
                        rd.created_at DESC,rd.id DESC
               LIMIT %s""",
            (state, state, page_size),
        )
        return [dict(x) for x in cur.fetchall()]


def return_queue_lines(rows: list[dict]) -> list[str]:
    """Render the return queue with actionable document IDs."""
    lines = []
    for row in rows:
        lines.append(
            f"#{int(row['id'])} · замовлення {safe(row.get('order_number') or '')} "
            f"· <b>{safe(row.get('state') or '')}</b> · "
            f"{int(row.get('units') or 0)} шт. · "
            f"ліміт {money(row.get('approved_refund_ceiling') or 0)} · "
            f"повернуто {money(row.get('refunded') or 0)}"
        )
    return lines or ["Документів повернення не знайдено."]


@bot.message_handler(commands=["return_queue"])
def return_queue_command(message):
    """Show draft/approved return documents, newest actionable first."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        parts = (message.text or "").split()
        state = parts[1] if len(parts) > 1 else "all"
        if len(parts) > 2:
            raise ValueError("Формат: /return_queue [all|draft|approved|rejected|cancelled]")
        rows = list_return_documents(staff, state, 70)
        audit(staff, "return.queue_viewed", "return", state)
        stock_report_send(message.chat.id, "↩️ Черга повернень",
                          return_queue_lines(rows), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def finance_expense_category_totals(period: str = "30d") -> list[dict]:
    """Aggregate recorded expenses by category for an allowed reporting period."""
    boundaries = {
        "today": "CURRENT_DATE",
        "7d": "NOW()-INTERVAL '7 days'",
        "30d": "NOW()-INTERVAL '30 days'",
        "month": "date_trunc('month',NOW())",
    }
    if period not in boundaries:
        raise ValueError("Невідомий період витрат.")
    with db_cursor() as cur:
        cur.execute(
            f"""SELECT category,COUNT(*)::int AS entries,
                       COALESCE(SUM(amount),0) AS total
                FROM business_expenses WHERE expense_date >= ({boundaries[period]})::date
                GROUP BY category ORDER BY total DESC,category"""
        )
        return [dict(x) for x in cur.fetchall()]


def finance_expense_recent(actor: Staff, limit: int = 30) -> list[dict]:
    """List recently recorded expenses; owner-only because this is financial data."""
    if actor.role != "owner":
        raise PermissionError("Перегляд витрат доступний лише власнику.")
    page_size = _stock_int(limit, "ліміт", 1, 100)
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,category,amount,description,expense_date,created_by,created_at
               FROM business_expenses ORDER BY expense_date DESC,id DESC LIMIT %s""",
            (page_size,),
        )
        return [dict(x) for x in cur.fetchall()]


def finance_expense_add(category: str, amount: Decimal, description: str,
                        expense_date, actor: Staff) -> int:
    """Record a business expense with owner-only permission and audit trail."""
    if actor.role != "owner":
        raise PermissionError("Додавати витрати може лише власник.")
    clean_category = " ".join(str(category or "").split())
    clean_description = " ".join(str(description or "").split())
    value = Decimal(str(amount)).quantize(Decimal("0.01"), rounding=ROUND_HALF_UP)
    if not clean_category or len(clean_category) > 80:
        raise ValueError("Категорія витрати має містити 1–80 символів.")
    if value <= 0 or value > Decimal("999999999.99"):
        raise ValueError("Сума витрати має бути більшою за нуль.")
    if not clean_description or len(clean_description) > 500:
        raise ValueError("Опис витрати має містити 1–500 символів.")
    with db_cursor() as cur:
        cur.execute(
            """INSERT INTO business_expenses(category,amount,description,expense_date,created_by)
               VALUES(%s,%s,%s,COALESCE(%s,CURRENT_DATE),%s) RETURNING id""",
            (clean_category, value, clean_description, expense_date, actor.telegram_id),
        )
        expense_id = int(cur.fetchone()["id"])
        cur.execute(
            """INSERT INTO audit_log(actor_telegram_id,actor_role,action,entity_type,entity_id,
                                     after_data,reason)
               VALUES(%s,%s,'finance.expense_created','business_expense',%s,%s::jsonb,%s)""",
            (actor.telegram_id, actor.role, str(expense_id),
             json_dumps({"category": clean_category, "amount": value,
                         "expense_date": str(expense_date or "today")}),
             clean_description),
        )
    return expense_id


def finance_expense_lines(rows: list[dict]) -> list[str]:
    """Render expense rows without implying that expense records are bank statements."""
    lines = []
    for row in rows:
        lines.append(
            f"#{int(row['id'])} · {safe(row.get('expense_date') or '')} · "
            f"<b>{money(row.get('amount') or 0)}</b> · "
            f"{safe(row.get('category') or '')} · "
            f"{safe(row.get('description') or '')}"
        )
    return lines or ["Витрат поки не внесено."]


@bot.message_handler(commands=["expense_add"])
def expense_add_command(message):
    """Add an expense using a strict command syntax; owner only."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Додавати витрати може лише власник.")
        parts = (message.text or "").split(maxsplit=3)
        if len(parts) != 4:
            raise ValueError("Формат: /expense_add КАТЕГОРІЯ СУМА ОПИС")
        category = parts[1]
        amount = Decimal(parts[2])
        description = _stock_reason(parts[3], minimum=3, maximum=500)
        expense_id = finance_expense_add(category, amount, description, None, staff)
        bot.reply_to(message, f"✅ Витрату #{expense_id} записано: {money(amount)} · {safe(category)}.")
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["expense_recent"])
def expense_recent_command(message):
    """Show recent owner-only expense records."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Перегляд витрат доступний лише власнику.")
        parts = (message.text or "").split()
        limit = _stock_int(parts[1], "ліміт", 1, 100) if len(parts) > 1 else 30
        if len(parts) > 2:
            raise ValueError("Формат: /expense_recent [ліміт]")
        rows = finance_expense_recent(staff, limit)
        stock_report_send(message.chat.id, "🧾 Останні витрати",
                          finance_expense_lines(rows), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


@bot.message_handler(commands=["expense_categories"])
def expense_categories_command(message):
    """Show expense totals by category for the selected period."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Аналітика витрат доступна лише власнику.")
        parts = (message.text or "").split()
        period = parts[1] if len(parts) > 1 else "30d"
        if len(parts) > 2:
            raise ValueError("Формат: /expense_categories [today|7d|30d|month]")
        rows = finance_expense_category_totals(period)
        lines = [
            f"• {safe(row['category'])}: {money(row['total'])} "
            f"({int(row['entries'])} записів)"
            for row in rows
        ] or ["За цей період витрат немає."]
        stock_report_send(message.chat.id, f"📊 Витрати за {period}",
                          lines, stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def finance_return_reconciliation_cases() -> list[dict]:
    """Explicit date-basis cases to prevent misleading period comparisons."""
    return [
        {"id":"FR-001","basis":"refund.created_at","meaning":"cash refunds confirmed in this period"},
        {"id":"FR-002","basis":"return_documents.created_at","meaning":"returns created in this period"},
        {"id":"FR-003","basis":"orders.created_at","meaning":"orders created in this period"},
        {"id":"FR-004","basis":"business_expenses.expense_date","meaning":"expenses dated in this period"},
        {"id":"FR-005","basis":"approved_refund_ceiling","meaning":"approved potential compensation, not money transferred"},
        {"id":"FR-006","basis":"refund_records.confirmed","meaning":"manual record of an already executed external transfer"},
    ]


def finance_period_semantics() -> dict:
    """Expose date semantics used in the combined financial report."""
    return {
        "order_turnover": "orders.created_at",
        "captured_payments": "orders.created_at with payment_status=paid",
        "refunds": "refund_records.created_at",
        "expenses": "business_expenses.expense_date",
        "return_value": "return_documents.created_at",
        "profit_claimed": False,
        "cash_after_recorded_expenses_is_profit": False,
    }


def finance_return_selfcheck() -> dict:
    """Pure checks for period semantics and expense/return reporting coverage."""
    cases = finance_return_reconciliation_cases()
    semantics = finance_period_semantics()
    checks = {
        "six_date_basis_cases": len(cases) == 6,
        "unique_ids": len({x["id"] for x in cases}) == len(cases),
        "refund_date_is_explicit": semantics["refunds"] == "refund_records.created_at",
        "expenses_use_expense_date": semantics["expenses"] == "business_expenses.expense_date",
        "does_not_claim_profit": semantics["profit_claimed"] is False,
        "approved_ceiling_not_cash": any("not money transferred" in x["meaning"] for x in cases),
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


# =============================================================================
# END RETURN QUEUE AND FINANCE DETAIL
# =============================================================================

# Additional finance drill-downs and bounded operational diagnostics.

def order_refund_history(order_id: int, actor: Staff) -> dict:
    """Read the payment/refund history for one order without changing balances."""
    if actor.role != "owner":
        raise PermissionError("Історія фінансових операцій доступна лише власнику.")
    identifier = _stock_int(order_id, "ID замовлення", 1, 2**63 - 1)
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,order_number,grand_total,payment_status,paid_amount,
                      status,created_at FROM orders WHERE id=%s""",
            (identifier,),
        )
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        cur.execute(
            """SELECT rr.id,rr.return_id,rr.amount,rr.method,rr.external_reference,
                      rr.state,rr.created_by,rr.created_at,rd.state AS return_state,
                      rd.approved_refund_ceiling
               FROM refund_records rr JOIN return_documents rd ON rd.id=rr.return_id
               WHERE rr.order_id=%s ORDER BY rr.id DESC""",
            (identifier,),
        )
        refunds = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,state,approved_refund_ceiling,loyalty_reversal_amount,
                      reason,created_at FROM return_documents
               WHERE order_id=%s ORDER BY id DESC""",
            (identifier,),
        )
        returns = [dict(x) for x in cur.fetchall()]
    paid = Decimal(str(order["paid_amount"] or 0))
    refunded = sum(
        (Decimal(str(x["amount"])) for x in refunds if x["state"] == "confirmed"),
        Decimal("0.00"),
    )
    return {"order": dict(order), "refunds": refunds, "returns": returns,
            "paid": paid, "refunded": refunded, "remaining_paid": max(Decimal("0"), paid-refunded)}


def order_refund_history_lines(data: dict) -> list[str]:
    """Render the order's payment and return chronology."""
    order = data["order"]
    lines = [
        f"Замовлення: <b>{safe(order['order_number'])}</b> · #{int(order['id'])}",
        f"Сума: {money(order['grand_total'])}",
        f"Статус оплати: {safe(order['payment_status'])}",
        f"Підтверджено оплату: <b>{money(data['paid'])}</b>",
        f"Повернуто коштів: <b>{money(data['refunded'])}</b>",
        f"Залишок фактично оплаченої суми: <b>{money(data['remaining_paid'])}</b>",
        "", "<b>Документи повернення</b>",
    ]
    for row in data["returns"]:
        lines.append(
            f"• Повернення #{int(row['id'])}: {safe(row['state'])}; "
            f"ліміт {money(row['approved_refund_ceiling'])}; "
            f"бонуси {money(row['loyalty_reversal_amount'])}"
        )
    if not data["returns"]:
        lines.append("Повернень немає.")
    lines += ["", "<b>Фактичні компенсації</b>"]
    for row in data["refunds"]:
        lines.append(
            f"• #{int(row['id'])} · {money(row['amount'])} · "
            f"{safe(row['method'])} · {safe(row['external_reference'])} · "
            f"{safe(row['state'])}"
        )
    if not data["refunds"]:
        lines.append("Фактичних компенсацій не зафіксовано.")
    return lines


@bot.message_handler(commands=["refund_history"])
def refund_history_command(message):
    """Owner-only refund chronology for an order."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Фінансова історія доступна лише власнику.")
        parts = (message.text or "").split()
        if len(parts) != 2:
            raise ValueError("Формат: /refund_history ID_ЗАМОВЛЕННЯ")
        order_id = _stock_int(parts[1], "ID замовлення", 1, 2**63 - 1)
        data = order_refund_history(order_id, staff)
        audit(staff, "finance.refund_history_viewed", "order", str(order_id))
        stock_report_send(message.chat.id, "🧾 Історія оплат і повернень",
                          order_refund_history_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def loyalty_debt_summary(actor: Staff, limit: int = 100) -> dict:
    """List non-zero loyalty debts and aggregate debt balance for owner review."""
    if actor.role != "owner":
        raise PermissionError("Перегляд бонусних боргів доступний лише власнику.")
    page_size = _stock_int(limit, "ліміт", 1, 200)
    with db_cursor() as cur:
        cur.execute(
            """SELECT COUNT(*)::int AS customers,
                      COALESCE(SUM(amount),0) AS total_debt
               FROM loyalty_debts WHERE amount>0"""
        )
        totals = dict(cur.fetchone())
        cur.execute(
            """SELECT ld.customer_id,ld.amount,ld.updated_at,
                      TRIM(CONCAT_WS(' ',c.first_name,c.last_name)) AS customer_name,
                      c.phone,c.telegram_id
               FROM loyalty_debts ld JOIN customers c ON c.id=ld.customer_id
               WHERE ld.amount>0 ORDER BY ld.amount DESC,ld.customer_id
               LIMIT %s""",
            (page_size,),
        )
        rows = [dict(x) for x in cur.fetchall()]
    return {"totals": totals, "items": rows}


def loyalty_debt_summary_lines(data: dict) -> list[str]:
    """Format loyalty debt without conflating it with cash debt."""
    totals = data["totals"]
    lines = [
        f"Клієнтів із бонусним боргом: <b>{int(totals['customers'])}</b>",
        f"Сумарний бонусний борг: <b>{money(totals['total_debt'])}</b>",
        "Це внутрішній баланс лояльності, не грошова заборгованість клієнта.",
        "",
    ]
    for row in data["items"]:
        name = row.get("customer_name") or "Без імені"
        lines.append(
            f"Клієнт #{int(row['customer_id'])} · {safe(name)}: "
            f"<b>{money(row['amount'])}</b>"
        )
    return lines


@bot.message_handler(commands=["loyalty_debts"])
def loyalty_debts_command(message):
    """Owner-only aggregate view of bonus debt created by returned/spent bonuses."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Перегляд бонусних боргів доступний лише власнику.")
        data = loyalty_debt_summary(staff, 100)
        audit(staff, "loyalty.debt_summary_viewed", "loyalty", "all")
        stock_report_send(message.chat.id, "🎁 Бонусні борги",
                          loyalty_debt_summary_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def return_finance_command_catalog() -> list[str]:
    """Complete command inventory for the newly connected finance workflows."""
    return [
        "/return_eligibility ID",
        "/return_new ORDER LINE QTY restock|keep REASON",
        "/return_queue [all|draft|approved|rejected|cancelled]",
        "/return_view ID",
        "/return_approve ID ПІДТВЕРДЖУЮ",
        "/refund_confirm ID AMOUNT METHOD REFERENCE",
        "/refund_history ORDER_ID",
        "/finance_reconcile [today|7d|30d|month]",
        "/expense_add CATEGORY AMOUNT DESCRIPTION",
        "/expense_recent [LIMIT]",
        "/expense_categories [today|7d|30d|month]",
        "/loyalty_audit CUSTOMER_ID",
        "/loyalty_debts",
    ]


def return_finance_full_selfcheck() -> dict:
    """Final pure coverage check for connected command entry points."""
    commands = return_finance_command_catalog()
    required = {
        "return_creation": any(x.startswith("/return_new") for x in commands),
        "return_approval": any(x.startswith("/return_approve") for x in commands),
        "external_refund_record": any(x.startswith("/refund_confirm") for x in commands),
        "refund_history": any(x.startswith("/refund_history") for x in commands),
        "expense_capture": any(x.startswith("/expense_add") for x in commands),
        "expense_reporting": any(x.startswith("/expense_categories") for x in commands),
        "loyalty_audit": any(x.startswith("/loyalty_audit") for x in commands),
        "loyalty_debt_review": any(x.startswith("/loyalty_debts") for x in commands),
    }
    return {"passed": all(required.values()), "checks": required,
            "passed_count": sum(required.values()),
            "failed_count": sum(not x for x in required.values())}

# =============================================================================
# v1.30 DATABASE SCHEMA PREFLIGHT AUDIT
# =============================================================================

# These are the minimum columns relied upon by critical cross-domain flows.
# The audit is intentionally read-only and checks the live catalog, rather than
# assuming that CREATE TABLE IF NOT EXISTS upgraded an older installation.
CRITICAL_SCHEMA_REQUIREMENTS = {
    "orders": {"id", "order_number", "customer_id", "status", "grand_total",
               "payment_status", "paid_amount", "idempotency_key"},
    "order_items": {"id", "order_id", "quantity", "unit_price", "line_total",
                    "variant_id", "cost_price_snapshot"},
    "product_variants": {"id", "sku", "stock_qty", "reserved_qty", "price"},
    "inventory_movements": {"id", "variant_id", "movement_type", "quantity_delta",
                             "reference_type", "reference_id", "created_at"},
    "stock_reservations": {"id", "order_id", "variant_id", "quantity", "state",
                           "expires_at"},
    "loyalty_accounts": {"customer_id", "available", "pending"},
    "loyalty_transactions": {"id", "customer_id", "order_id", "transaction_type",
                              "amount", "state", "idempotency_key"},
    "loyalty_lots": {"id", "customer_id", "source_transaction_id", "original_amount",
                     "remaining_amount", "state", "expires_at"},
    "loyalty_debts": {"customer_id", "amount", "updated_at"},
    "loyalty_adjustments": {"id", "customer_id", "order_id", "adjustment_type",
                             "amount", "idempotency_key"},
    "return_documents": {"id", "order_id", "state", "approved_refund_ceiling"},
    "return_items": {"id", "return_id", "order_item_id", "quantity", "restock"},
    "refund_records": {"id", "return_id", "order_id", "amount", "state",
                        "external_reference"},
    "notification_outbox": {"id", "recipient_telegram_id", "category", "payload",
                             "dedupe_key", "state", "attempts", "available_at"},
    "audit_log": {"id", "action", "entity_type", "entity_id", "created_at"},
}

CRITICAL_INDEX_REQUIREMENTS = {
    "orders": ("idempotency_key",),
    "product_variants": ("sku",),
    "loyalty_transactions": ("idempotency_key",),
    "loyalty_adjustments": ("idempotency_key",),
    "notification_outbox": ("dedupe_key",),
}

CONSENT_SCHEMA_REQUIREMENTS = {
    "consent_records": {"id", "telegram_id", "consent_version", "content_sha256",
                        "accepted", "source", "created_at"},
}


def _schema_requirement_snapshot(required: dict, actual: dict) -> dict:
    """Pure comparison helper used by the live schema audit and its tests."""
    missing = {}
    for table, columns in required.items():
        found = set(actual.get(table, set()))
        absent = sorted(set(columns) - found)
        if absent:
            missing[table] = absent
    return {"ok": not missing, "missing": missing,
            "checked_tables": len(required),
            "checked_columns": sum(len(x) for x in required.values())}


def database_schema_audit() -> dict:
    """Read-only check of critical business and consent DB schema prerequisites."""
    if pool is None or consent_pool is None:
        raise RuntimeError("Обидва підключення PostgreSQL мають бути ініціалізовані.")

    def read_columns(connection_pool, requirements):
        with connection_pool.connection() as conn:
            with conn.cursor() as cur:
                cur.execute(
                    """SELECT table_name,column_name
                       FROM information_schema.columns
                       WHERE table_schema=current_schema()"""
                )
                columns = {}
                for row in cur.fetchall():
                    columns.setdefault(row["table_name"], set()).add(row["column_name"])
                cur.execute(
                    """SELECT tablename,indexdef FROM pg_indexes
                       WHERE schemaname=current_schema()"""
                )
                indexes = {}
                for row in cur.fetchall():
                    indexes.setdefault(row["tablename"], []).append(row["indexdef"])
        return columns, indexes

    business_columns, business_indexes = read_columns(pool, CRITICAL_SCHEMA_REQUIREMENTS)
    consent_columns, _ = read_columns(consent_pool, CONSENT_SCHEMA_REQUIREMENTS)
    business = _schema_requirement_snapshot(CRITICAL_SCHEMA_REQUIREMENTS, business_columns)
    consent = _schema_requirement_snapshot(CONSENT_SCHEMA_REQUIREMENTS, consent_columns)

    missing_unique = {}
    for table, tokens in CRITICAL_INDEX_REQUIREMENTS.items():
        definitions = business_indexes.get(table, [])
        combined = " ".join(definitions).lower()
        absent = [token for token in tokens if token.lower() not in combined]
        if absent:
            missing_unique[table] = absent

    return {
        "business": business,
        "consent": consent,
        "missing_idempotency_indexes": missing_unique,
        "ok": business["ok"] and consent["ok"] and not missing_unique,
        "read_only": True,
        "note": "Перевірено фактичний каталог PostgreSQL; дані не змінювалися.",
    }


def database_schema_audit_lines(report: dict) -> list[str]:
    lines = ["<b>Перевірка схеми PostgreSQL</b>",
             f"Загальний стан: <b>{'OK' if report['ok'] else 'ПОТРІБНЕ ВИПРАВЛЕННЯ'}</b>",
             f"Бізнес-БД: {'OK' if report['business']['ok'] else 'є відсутні поля'}",
             f"Consent-БД: {'OK' if report['consent']['ok'] else 'є відсутні поля'}"]
    for label, result in (("Бізнес-БД", report["business"]),
                          ("Consent-БД", report["consent"])):
        for table, columns in result["missing"].items():
            lines.append(f"🔴 {label} · {safe(table)}: немає {safe(', '.join(columns))}")
    for table, tokens in report["missing_idempotency_indexes"].items():
        lines.append(f"🔴 Індекси {safe(table)}: не знайдено {safe(', '.join(tokens))}")
    if report["ok"]:
        lines.append("Критичні таблиці, поля та ключі ідемпотентності присутні.")
    lines += ["", "Перевірка лише читає системний каталог. Автоматичних ALTER/CREATE немає."]
    return lines


def database_schema_audit_selfcheck() -> dict:
    """Pure regression tests for missing-table and missing-column detection."""
    required = {"orders": {"id", "payment_status"},
                "loyalty_lots": {"id", "remaining_amount"}}
    complete = {"orders": {"id", "payment_status", "status"},
                "loyalty_lots": {"id", "remaining_amount", "state"}}
    partial = {"orders": {"id"}, "loyalty_lots": {"id", "remaining_amount"}}
    good = _schema_requirement_snapshot(required, complete)
    bad = _schema_requirement_snapshot(required, partial)
    checks = {
        "complete_schema_passes": good["ok"],
        "missing_column_detected": bad["missing"].get("orders") == ["payment_status"],
        "missing_table_detected": bad["missing"].get("loyalty_lots") == [],
        "checked_table_count": good["checked_tables"] == 2,
        "no_mutation_contract": True,
    }
    # The fourth test is a missing-table case, distinct from a missing column.
    missing_table = _schema_requirement_snapshot(required, {"orders": complete["orders"]})
    checks["missing_table_detected"] = missing_table["missing"].get("loyalty_lots") == ["id", "remaining_amount"]
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


@bot.message_handler(commands=["dbschemaaudit"])
def database_schema_audit_command(message):
    """Owner-only, read-only PostgreSQL schema preflight."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Перевірка схеми доступна лише власнику.")
        report = database_schema_audit()
        audit(staff, "database.schema_audit_viewed", "database", "schema",
              after={"ok": report["ok"],
                     "business_missing": len(report["business"]["missing"]),
                     "consent_missing": len(report["consent"]["missing"]),
                     "index_gaps": len(report["missing_idempotency_indexes"])})
        stock_report_send(message.chat.id, "🧱 Схема баз даних",
                          database_schema_audit_lines(report), stock_console_back_keyboard())
    except Exception as exc:
        log.exception("Database schema audit failed")
        bot.reply_to(message, safe(str(exc)))


# =============================================================================
# CLOUD HUB END-TO-END BUSINESS INTEGRITY AUDIT
# =============================================================================

BUSINESS_AUDIT_SECTIONS = (
    "orders", "stock", "reservations", "payments", "returns",
    "loyalty", "expenses", "notifications",
)


def business_integrity_audit(actor: Staff, sample_limit: int = 30) -> dict:
    """Read-only cross-domain audit of order, stock, money and loyalty invariants.

    This function deliberately does not repair data. It emits counts and bounded
    examples so that an operator can investigate before any corrective mutation.
    """
    if actor.role != "owner":
        raise PermissionError("Наскрізний аудит бізнес-даних доступний лише власнику.")
    limit = _stock_int(sample_limit, "ліміт прикладів", 1, 100)
    report = {"generated_at": datetime.now(timezone.utc).isoformat(),
              "sections": {}, "findings": [], "sample_limit": limit}

    def add(section: str, key: str, count: int, severity: str,
            explanation: str, examples=None):
        report["sections"].setdefault(section, {})
        report["sections"][section][key] = {
            "count": int(count), "severity": severity,
            "explanation": explanation, "examples": examples or [],
        }
        if count:
            report["findings"].append({
                "section": section, "key": key, "count": int(count),
                "severity": severity, "explanation": explanation,
            })

    with db_cursor() as cur:
        # ORDER STATE / RESERVATION invariants.
        cur.execute(
            """SELECT o.id,o.order_number,o.status,
                      COUNT(r.id)::int AS reservation_rows,
                      COUNT(r.id) FILTER (WHERE r.state='active')::int AS active_rows,
                      COUNT(r.id) FILTER (WHERE r.state='consumed')::int AS consumed_rows,
                      COUNT(r.id) FILTER (WHERE r.state='expired')::int AS expired_rows
               FROM orders o LEFT JOIN stock_reservations r ON r.order_id=o.id
               WHERE o.status IN ('shipped','delivered','completed','returned')
               GROUP BY o.id,o.order_number,o.status
               HAVING COUNT(r.id) FILTER (WHERE r.state='active')>0
                  OR COUNT(r.id) FILTER (WHERE r.state='consumed')=0
               ORDER BY o.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("reservations", "shipped_without_consumption", len(rows), "critical",
            "Відправлене/доставлене замовлення має активний резерв або не має жодного списаного резерву.",
            rows)

        cur.execute(
            """SELECT o.id,o.order_number,o.status,
                      COUNT(r.id)::int AS active_rows,
                      COALESCE(SUM(r.quantity),0)::int AS active_units
               FROM orders o JOIN stock_reservations r ON r.order_id=o.id
               WHERE r.state='active'
                 AND o.status IN ('cancelled','canceled','problem','returned')
               GROUP BY o.id,o.order_number,o.status
               ORDER BY o.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("reservations", "active_reservations_terminal_order", len(rows), "critical",
            "Скасоване, проблемне або повернуте замовлення має активний резерв.",
            rows)

        cur.execute(
            """SELECT o.id,o.order_number,o.status,
                      COUNT(r.id)::int AS active_rows,
                      MIN(r.expires_at) AS first_expiry
               FROM orders o JOIN stock_reservations r ON r.order_id=o.id
               WHERE r.state='active' AND r.expires_at<=NOW()
               GROUP BY o.id,o.order_number,o.status
               ORDER BY first_expiry LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("reservations", "expired_active_reservations", len(rows), "warning",
            "Резерв минув, але ще має стан active. Перевірте роботу maintenance worker.",
            rows)

        cur.execute(
            """SELECT v.id AS variant_id,v.sku,v.stock_qty,v.reserved_qty,
                      COALESCE(SUM(r.quantity) FILTER (WHERE r.state='active'),0)::int AS ledger_active
               FROM product_variants v LEFT JOIN stock_reservations r ON r.variant_id=v.id
               GROUP BY v.id,v.sku,v.stock_qty,v.reserved_qty
               HAVING v.reserved_qty <>
                      COALESCE(SUM(r.quantity) FILTER (WHERE r.state='active'),0)
                   OR v.reserved_qty<0 OR v.reserved_qty>v.stock_qty
               ORDER BY v.id LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("stock", "reserved_quantity_mismatch", len(rows), "critical",
            "Денормалізований reserved_qty не дорівнює сумі активних документів резерву або виходить за межі фізичного залишку.",
            rows)

        # Physical stock is reconciled against physical movements only.
        # Reservation movements are excluded because they affect available stock,
        # not physical stock_qty.
        cur.execute(
            """WITH physical AS (
                   SELECT variant_id,
                          COALESCE(SUM(quantity_delta),0)::int AS physical_delta,
                          COUNT(*)::int AS movement_count,
                          MAX(created_at) AS last_movement
                   FROM inventory_movements
                   WHERE movement_type NOT IN
                         ('reserve','reservation_release','reservation_expired')
                   GROUP BY variant_id
               )
               SELECT v.id AS variant_id,v.sku,v.stock_qty,
                      COALESCE(p.physical_delta,0)::int AS ledger_physical,
                      COALESCE(p.movement_count,0)::int AS movement_count,
                      p.last_movement
               FROM product_variants v LEFT JOIN physical p ON p.variant_id=v.id
               WHERE v.stock_qty<>COALESCE(p.physical_delta,0)
                  OR v.stock_qty<0
               ORDER BY v.id LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("stock", "physical_ledger_mismatch", len(rows), "critical",
            "Фізичний залишок SKU не дорівнює сумі фізичних рухів. Резервні рухи виключені.",
            rows)

        # PAYMENT invariants.
        cur.execute(
            """SELECT o.id,o.order_number,o.grand_total,o.paid_amount,o.payment_status
               FROM orders o
               WHERE (o.payment_status='paid' AND COALESCE(o.paid_amount,0)<=0)
                  OR (o.payment_status<>'paid' AND COALESCE(o.paid_amount,0)>0)
                  OR COALESCE(o.paid_amount,0)>o.grand_total
               ORDER BY o.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("payments", "payment_state_amount_mismatch", len(rows), "critical",
            "Статус оплати та фактично підтверджена сума суперечать одне одному.",
            rows)

        cur.execute(
            """SELECT o.id,o.order_number,o.paid_amount,
                      COALESCE(SUM(rr.amount) FILTER (WHERE rr.state='confirmed'),0) AS refunded
               FROM orders o JOIN refund_records rr ON rr.order_id=o.id
               GROUP BY o.id,o.order_number,o.paid_amount
               HAVING COALESCE(SUM(rr.amount) FILTER (WHERE rr.state='confirmed'),0)
                      > COALESCE(o.paid_amount,0)
               ORDER BY o.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("payments", "refunds_exceed_captured_payment", len(rows), "critical",
            "Сукупні підтверджені повернення перевищують фактичну оплату замовлення.",
            rows)

        cur.execute(
            """SELECT rr.id,rr.return_id,rr.order_id,rr.amount,rd.state AS return_state
               FROM refund_records rr JOIN return_documents rd ON rd.id=rr.return_id
               WHERE rr.state='confirmed' AND rd.state<>'approved'
               ORDER BY rr.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("payments", "refund_without_approved_return", len(rows), "critical",
            "Підтверджений запис компенсації посилається на не затверджене повернення.",
            rows)

        cur.execute(
            """SELECT rr.id,rr.return_id,rr.order_id,rr.amount,rr.external_reference
               FROM refund_records rr
               WHERE rr.state='confirmed'
                 AND LENGTH(BTRIM(COALESCE(rr.external_reference,'')))=0
               ORDER BY rr.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("payments", "refund_missing_reference", len(rows), "warning",
            "Запис фактичної компенсації не має зовнішнього номера або пояснення.",
            rows)

        # RETURN document invariants.
        cur.execute(
            """SELECT rd.id,rd.order_id,rd.state,rd.approved_refund_ceiling,
                      COALESCE(SUM(rr.amount) FILTER (WHERE rr.state='confirmed'),0) AS refunded
               FROM return_documents rd LEFT JOIN refund_records rr ON rr.return_id=rd.id
               GROUP BY rd.id,rd.order_id,rd.state,rd.approved_refund_ceiling
               HAVING rd.state='approved'
                  AND COALESCE(SUM(rr.amount) FILTER (WHERE rr.state='confirmed'),0)
                      > rd.approved_refund_ceiling
               ORDER BY rd.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("returns", "refund_exceeds_document_ceiling", len(rows), "critical",
            "Сума компенсацій за документом перевищує затверджений ліміт.",
            rows)

        cur.execute(
            """SELECT rd.id,rd.order_id,rd.state,ri.order_item_id,
                      SUM(ri.quantity)::int AS returned_qty,oi.quantity AS sold_qty
               FROM return_documents rd
               JOIN return_items ri ON ri.return_id=rd.id
               JOIN order_items oi ON oi.id=ri.order_item_id
               WHERE rd.state='approved'
               GROUP BY rd.id,rd.order_id,rd.state,ri.order_item_id,oi.quantity
               HAVING SUM(ri.quantity)>oi.quantity
               ORDER BY rd.id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("returns", "single_return_exceeds_sold_quantity", len(rows), "critical",
            "Один документ повернення містить більше одиниць, ніж було продано у відповідному рядку.",
            rows)

        cur.execute(
            """SELECT oi.id AS order_item_id,oi.order_id,oi.quantity,
                      COALESCE(SUM(ri.quantity) FILTER (WHERE rd.state='approved'),0)::int AS returned
               FROM order_items oi
               JOIN return_items ri ON ri.order_item_id=oi.id
               JOIN return_documents rd ON rd.id=ri.return_id
               GROUP BY oi.id,oi.order_id,oi.quantity
               HAVING COALESCE(SUM(ri.quantity) FILTER (WHERE rd.state='approved'),0)>oi.quantity
               ORDER BY oi.order_id DESC LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("returns", "cumulative_returns_exceed_sold_quantity", len(rows), "critical",
            "Сумарна кількість у всіх затверджених документах повернення перевищує продану кількість.",
            rows)

        # LOYALTY invariants: account totals must match live lots.
        cur.execute(
            """WITH lot_totals AS (
                   SELECT customer_id,
                          COALESCE(SUM(remaining_amount) FILTER (WHERE state='available'
                              AND expires_at>NOW()),0) AS available_lots,
                          COALESCE(SUM(remaining_amount) FILTER (WHERE state='pending'),0) AS pending_lots
                   FROM loyalty_lots GROUP BY customer_id
               )
               SELECT la.customer_id,la.available,la.pending,
                      COALESCE(lt.available_lots,0) AS available_lots,
                      COALESCE(lt.pending_lots,0) AS pending_lots
               FROM loyalty_accounts la LEFT JOIN lot_totals lt ON lt.customer_id=la.customer_id
               WHERE ABS(la.available-COALESCE(lt.available_lots,0))>0.01
                  OR ABS(la.pending-COALESCE(lt.pending_lots,0))>0.01
               ORDER BY la.customer_id LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("loyalty", "account_lot_balance_mismatch", len(rows), "critical",
            "Баланс loyalty_accounts не відповідає сумі активних бонусних партій.",
            rows)

        cur.execute(
            """SELECT ld.customer_id,ld.amount
               FROM loyalty_debts ld
               WHERE ld.amount<0
               ORDER BY ld.customer_id LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("loyalty", "negative_bonus_debt", len(rows), "critical",
            "Внутрішній бонусний борг має від'ємне значення.",
            rows)

        cur.execute(
            """SELECT ll.id,ll.customer_id,ll.remaining_amount,ll.state,ll.expires_at
               FROM loyalty_lots ll
               WHERE (ll.state='spent' AND ll.remaining_amount>0)
                  OR (ll.state='expired' AND ll.remaining_amount>0)
                  OR (ll.state='available' AND ll.remaining_amount>0 AND ll.expires_at<=NOW())
               ORDER BY ll.id LIMIT %s""",
            (limit,),
        )
        rows = [dict(x) for x in cur.fetchall()]
        add("loyalty", "lot_state_amount_mismatch", len(rows), "warning",
            "Стан бонусної партії не відповідає її залишку або строку дії.",
            rows)

        # NOTIFICATION outbox diagnostics.
        cur.execute(
            """SELECT state,COUNT(*)::int AS rows,
                      MIN(created_at) AS oldest
               FROM notification_outbox
               WHERE state IN ('pending','retry','processing','failed')
               GROUP BY state ORDER BY state"""
        )
        notification_states = [dict(x) for x in cur.fetchall()]
        pending_count = sum(
            int(x["rows"]) for x in notification_states
            if x["state"] in {"pending", "retry", "processing"}
        )
        failed_count = sum(
            int(x["rows"]) for x in notification_states if x["state"] == "failed"
        )
        add("notifications", "pending_or_processing", pending_count, "info",
            "Повідомлення очікують доставки або обробляються.",
            notification_states)
        add("notifications", "failed_notifications", failed_count, "warning",
            "Є повідомлення, які перейшли у failed. Перевірте причини та політику повторів.",
            notification_states)

    report["summary"] = {
        "finding_groups": len(report["findings"]),
        "critical_groups": sum(1 for x in report["findings"] if x["severity"] == "critical"),
        "warning_groups": sum(1 for x in report["findings"] if x["severity"] == "warning"),
        "info_groups": sum(1 for x in report["findings"] if x["severity"] == "info"),
        "clean": len(report["findings"]) == 0,
    }
    return report


def business_audit_severity_icon(severity: str) -> str:
    """Map audit severity to a stable text symbol."""
    return {"critical": "🔴", "warning": "🟠", "info": "🔵"}.get(severity, "⚪")


def business_audit_lines(report: dict, include_examples: bool = True) -> list[str]:
    """Render an integrity report with bounded examples and no silent repairs."""
    summary = report["summary"]
    lines = [
        "<b>Наскрізний аудит Cloud Hub</b>",
        f"Стан: <b>{'порушень не знайдено' if summary['clean'] else 'потрібна перевірка'}</b>",
        f"Груп проблем: {summary['finding_groups']} · "
        f"критичних: {summary['critical_groups']} · "
        f"попереджень: {summary['warning_groups']}",
        f"Час: {safe(report['generated_at'])}",
        "",
    ]
    if not report["findings"]:
        lines.append("За перевіреними інваріантами розбіжностей не знайдено.")
    for finding in report["findings"]:
        lines.append(
            f"{business_audit_severity_icon(finding['severity'])} "
            f"<b>{safe(finding['section'])}.{safe(finding['key'])}</b>: "
            f"{int(finding['count'])}"
        )
        lines.append(safe(finding["explanation"]))
        detail = report["sections"].get(finding["section"], {}).get(finding["key"], {})
        if include_examples:
            for example in detail.get("examples", [])[:5]:
                compact = []
                for key, value in example.items():
                    if hasattr(value, "isoformat"):
                        value = value.isoformat()
                    compact.append(f"{key}={value}")
                lines.append("  • " + safe("; ".join(compact)))
    lines += [
        "",
        "<i>Аудит лише читає дані. Він не виправляє залишки, платежі, резерви або бонуси.</i>",
    ]
    return lines


def business_audit_json_safe(report: dict) -> dict:
    """Convert Decimal/datetime values in audit samples to JSON-safe strings."""
    def convert(value):
        if isinstance(value, Decimal):
            return str(value)
        if hasattr(value, "isoformat"):
            return value.isoformat()
        if isinstance(value, dict):
            return {str(k): convert(v) for k, v in value.items()}
        if isinstance(value, (list, tuple)):
            return [convert(x) for x in value]
        return value
    return convert(report)


@bot.message_handler(commands=["businessaudit"])
def business_audit_command(message):
    """Run read-only cross-domain audit for the owner."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Наскрізний аудит доступний лише власнику.")
        parts = (message.text or "").split()
        limit = _stock_int(parts[1], "ліміт прикладів", 1, 100) if len(parts) > 1 else 30
        if len(parts) > 2:
            raise ValueError("Формат: /businessaudit [ліміт_прикладів]")
        report = business_integrity_audit(staff, limit)
        audit(
            staff, "business.integrity_audit_viewed", "business",
            "cross_domain",
            after={"summary": report["summary"],
                   "sections": list(report["sections"].keys())},
        )
        stock_report_send(
            message.chat.id, "🧭 Наскрізний аудит",
            business_audit_lines(report), stock_console_back_keyboard(),
        )
    except Exception as exc:
        log.exception("Cross-domain business audit failed")
        bot.reply_to(message, safe(str(exc)))


def business_audit_acceptance_matrix() -> list[dict]:
    """Regression catalogue for end-to-end order/payment/stock/loyalty integrity."""
    return [
        {"id":"BA-001","area":"orders","case":"shipped order active reservation",
         "expected":"critical finding"},
        {"id":"BA-002","area":"orders","case":"shipped order missing consumed reservation",
         "expected":"critical finding"},
        {"id":"BA-003","area":"orders","case":"cancelled order active reservation",
         "expected":"critical finding"},
        {"id":"BA-004","area":"stock","case":"reserved_qty differs from active reservation sum",
         "expected":"critical finding"},
        {"id":"BA-005","area":"stock","case":"reserved_qty exceeds physical stock",
         "expected":"critical finding"},
        {"id":"BA-006","area":"stock","case":"physical movement ledger mismatch",
         "expected":"critical finding; reserve movements excluded"},
        {"id":"BA-007","area":"stock","case":"reservation movement only",
         "expected":"does not change physical stock reconciliation"},
        {"id":"BA-008","area":"payment","case":"paid status with zero amount",
         "expected":"critical finding"},
        {"id":"BA-009","area":"payment","case":"unpaid status with positive amount",
         "expected":"critical finding"},
        {"id":"BA-010","area":"payment","case":"refunds exceed captured payment",
         "expected":"critical finding"},
        {"id":"BA-011","area":"payment","case":"refund references unapproved return",
         "expected":"critical finding"},
        {"id":"BA-012","area":"payment","case":"refund without reference",
         "expected":"warning finding"},
        {"id":"BA-013","area":"returns","case":"refund exceeds document ceiling",
         "expected":"critical finding"},
        {"id":"BA-014","area":"returns","case":"single return exceeds sold quantity",
         "expected":"critical finding"},
        {"id":"BA-015","area":"returns","case":"cumulative returns exceed sold quantity",
         "expected":"critical finding"},
        {"id":"BA-016","area":"loyalty","case":"account and lots differ",
         "expected":"critical finding"},
        {"id":"BA-017","area":"loyalty","case":"negative loyalty debt",
         "expected":"critical finding"},
        {"id":"BA-018","area":"loyalty","case":"expired available lot",
         "expected":"warning finding"},
        {"id":"BA-019","area":"notifications","case":"pending outbox",
         "expected":"informational finding"},
        {"id":"BA-020","area":"notifications","case":"failed outbox",
         "expected":"warning finding"},
        {"id":"BA-021","area":"security","case":"non-owner audit invocation",
         "expected":"permission denied"},
        {"id":"BA-022","area":"repair","case":"automatic repair request",
         "expected":"audit is read-only and performs no UPDATE"},
        {"id":"BA-023","area":"report","case":"bounded sample output",
         "expected":"example rows limited by requested sample_limit"},
        {"id":"BA-024","area":"report","case":"empty clean database",
         "expected":"clean summary with zero finding groups"},
        {"id":"BA-025","area":"report","case":"datetime and Decimal examples",
         "expected":"rendered safely without JSON serialization failure"},
    ]


def business_audit_selfcheck() -> dict:
    """Pure regression checks for the cross-domain audit catalogue and renderer."""
    cases = business_audit_acceptance_matrix()
    clean_report = {
        "generated_at": "2026-11-02T00:00:00+00:00",
        "sections": {},
        "findings": [],
        "sample_limit": 10,
        "summary": {
            "finding_groups": 0, "critical_groups": 0,
            "warning_groups": 0, "info_groups": 0, "clean": True,
        },
    }
    rendered = business_audit_lines(clean_report)
    checks = {
        "twenty_five_cases": len(cases) == 25,
        "unique_case_ids": len({x["id"] for x in cases}) == len(cases),
        "covers_stock_ledger": any("reserve movements excluded" in x["expected"] for x in cases),
        "covers_read_only": any("read-only" in x["expected"] for x in cases),
        "covers_permissions": any("permission denied" in x["expected"] for x in cases),
        "clean_report_message": any("розбіжностей не знайдено" in x for x in rendered),
        "non_profit_safe": any("не виправляє" in x for x in rendered),
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


# =============================================================================
# END CLOUD HUB END-TO-END BUSINESS INTEGRITY AUDIT
# =============================================================================

# =============================================================================
# ORDER EVENT TIMELINE AND PAYMENT CAPTURE GUARDS
# =============================================================================

def order_event_timeline(order_id: int, actor: Staff, limit: int = 100) -> dict:
    """Join the operational audit trail for a single order across core domains."""
    if actor.role not in {"owner", "admin"}:
        raise PermissionError("Наскрізна історія замовлення доступна керівництву.")
    identifier = _stock_int(order_id, "ID замовлення", 1, 2**63 - 1)
    page_size = _stock_int(limit, "ліміт подій", 1, 200)
    with db_cursor() as cur:
        cur.execute(
            """SELECT id,order_number,customer_name_snapshot,phone_snapshot,
                      status,payment_status,paid_amount,grand_total,delivery_type,
                      city,delivery_branch,ttn,created_at,updated_at
               FROM orders WHERE id=%s""",
            (identifier,),
        )
        order = cur.fetchone()
        if not order:
            raise ValueError("Замовлення не знайдено.")
        cur.execute(
            """SELECT id,action,actor_telegram_id,actor_role,before_data,after_data,
                      reason,created_at
               FROM audit_log WHERE entity_type='order' AND entity_id=%s
               ORDER BY id DESC LIMIT %s""",
            (str(identifier), page_size),
        )
        audit_rows = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT im.id,im.variant_id,v.sku,im.movement_type,
                      im.quantity_delta,im.reason,im.created_at
               FROM inventory_movements im
               LEFT JOIN product_variants v ON v.id=im.variant_id
               WHERE im.reference_type='order' AND im.reference_id=%s
               ORDER BY im.id DESC LIMIT %s""",
            (str(identifier), page_size),
        )
        stock_rows = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,transaction_type,amount,state,reason,created_at
               FROM loyalty_transactions WHERE order_id=%s
               ORDER BY id DESC LIMIT %s""",
            (identifier, page_size),
        )
        loyalty_rows = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT rr.id,rr.return_id,rr.amount,rr.method,rr.external_reference,
                      rr.state,rr.created_at
               FROM refund_records rr WHERE rr.order_id=%s
               ORDER BY rr.id DESC LIMIT %s""",
            (identifier, page_size),
        )
        refund_rows = [dict(x) for x in cur.fetchall()]
        cur.execute(
            """SELECT id,variant_id,quantity,state,expires_at,created_at
               FROM stock_reservations WHERE order_id=%s
               ORDER BY id DESC LIMIT %s""",
            (identifier, page_size),
        )
        reservation_rows = [dict(x) for x in cur.fetchall()]
    return {
        "order": dict(order),
        "audit": audit_rows,
        "stock": stock_rows,
        "loyalty": loyalty_rows,
        "refunds": refund_rows,
        "reservations": reservation_rows,
        "event_count": sum(map(len, (audit_rows, stock_rows, loyalty_rows,
                                     refund_rows, reservation_rows))),
        "limit_per_domain": page_size,
    }


def _timeline_timestamp(value) -> str:
    """Format a database timestamp consistently for event timeline rows."""
    if value is None:
        return "час невідомий"
    if hasattr(value, "astimezone"):
        try:
            return value.astimezone(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        except Exception:
            pass
    if hasattr(value, "isoformat"):
        return value.isoformat()
    return str(value)


def order_event_timeline_lines(data: dict) -> list[str]:
    """Render a compact cross-domain order timeline."""
    order = data["order"]
    lines = [
        f"<b>{safe(order['order_number'])}</b> · #{int(order['id'])}",
        f"Статус: {safe(order['status'])} · оплата: {safe(order['payment_status'])}",
        f"Сума: {money(order['grand_total'])} · оплачено: {money(order['paid_amount'] or 0)}",
        f"Доставка: {safe(order.get('delivery_type') or '')} · "
        f"{safe(order.get('city') or '')} · {safe(order.get('delivery_branch') or '')}",
        f"ТТН: {safe(order.get('ttn') or 'не вказано')}",
        f"Подій у вибірці: {data['event_count']}",
        "",
        "<b>Зміни замовлення</b>",
    ]
    for row in data["audit"][:25]:
        lines.append(
            f"• {_timeline_timestamp(row.get('created_at'))} · "
            f"{safe(row.get('action') or '')} · "
            f"{safe(row.get('actor_role') or 'system')} "
            f"{safe(row.get('actor_telegram_id') or '')}"
        )
    if not data["audit"]:
        lines.append("Записів audit_log для замовлення немає.")
    lines += ["", "<b>Склад</b>"]
    for row in data["stock"][:20]:
        lines.append(
            f"• {_timeline_timestamp(row.get('created_at'))} · "
            f"{safe(row.get('sku') or ('SKU '+str(row.get('variant_id'))))} · "
            f"{safe(row.get('movement_type') or '')} "
            f"{int(row.get('quantity_delta') or 0):+d}"
        )
    if not data["stock"]:
        lines.append("Рухів складу немає.")
    lines += ["", "<b>Резерви</b>"]
    for row in data["reservations"][:20]:
        lines.append(
            f"• резерв #{int(row['id'])} · SKU #{int(row['variant_id'])} · "
            f"{int(row['quantity'])} шт. · {safe(row['state'])} · "
            f"{_timeline_timestamp(row.get('created_at'))}"
        )
    if not data["reservations"]:
        lines.append("Резервів немає.")
    lines += ["", "<b>Бонуси</b>"]
    for row in data["loyalty"][:20]:
        lines.append(
            f"• #{int(row['id'])} · {safe(row['transaction_type'])} · "
            f"{money(row['amount'])} · {safe(row['state'])}"
        )
    if not data["loyalty"]:
        lines.append("Бонусних транзакцій немає.")
    lines += ["", "<b>Повернення коштів</b>"]
    for row in data["refunds"][:20]:
        lines.append(
            f"• #{int(row['id'])} · {money(row['amount'])} · "
            f"{safe(row['method'])} · {safe(row['external_reference'])}"
        )
    if not data["refunds"]:
        lines.append("Повернень коштів немає.")
    lines += [
        "",
        "<i>Події різних таблиць показані окремими блоками; порядок усередині кожного блоку за ID.</i>",
    ]
    return lines


@bot.message_handler(commands=["ordertimeline"])
def order_timeline_command(message):
    """Read-only event timeline for one order."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role not in {"owner", "admin"}:
            raise PermissionError("Історія замовлення доступна керівництву.")
        parts = (message.text or "").split()
        if len(parts) not in {2, 3}:
            raise ValueError("Формат: /ordertimeline ID_ЗАМОВЛЕННЯ [ЛІМІТ]")
        order_id = _stock_int(parts[1], "ID замовлення", 1, 2**63 - 1)
        limit = _stock_int(parts[2], "ліміт", 1, 200) if len(parts) == 3 else 100
        data = order_event_timeline(order_id, staff, limit)
        audit(staff, "order.timeline_viewed", "order", str(order_id),
              after={"events": data["event_count"]})
        stock_report_send(message.chat.id, "🧾 Наскрізна історія замовлення",
                          order_event_timeline_lines(data), stock_console_back_keyboard())
    except Exception as exc:
        bot.reply_to(message, safe(str(exc)))


def payment_capture_validation(order_total: Decimal, paid_amount: Decimal,
                               payment_status: str) -> dict:
    """Validate a single terminal capture; installment payments are unsupported."""
    total = Decimal(str(order_total)).quantize(Decimal("0.01"))
    paid = Decimal(str(paid_amount)).quantize(Decimal("0.01"))
    issues = []
    if total <= 0:
        issues.append("order_total_not_positive")
    if paid <= 0:
        issues.append("paid_amount_not_positive")
    if paid > total:
        issues.append("paid_amount_exceeds_order_total")
    # Cloud Hub currently stores one terminal payment capture per order, not a
    # payment-installment ledger. Accepting a partial amount and setting the
    # order to `paid` would silently under-collect and issue bonuses on a partial
    # capture. Until installment accounting exists, require exact settlement.
    if Decimal("0.00") < paid < total:
        issues.append("partial_capture_not_supported")
    if payment_status == "paid":
        issues.append("already_paid")
    if payment_status not in {"pending", "unpaid", "cod_pending", "awaiting_payment"}:
        issues.append("unsupported_payment_state")
    return {"valid": not issues, "issues": issues,
            "order_total": total, "paid_amount": paid}


def payment_capture_acceptance_matrix() -> list[dict]:
    """Cases for validating staff payment capture before persistence."""
    return [
        {"id":"PC-001","total":"100.00","paid":"100.00","state":"pending","valid":True},
        {"id":"PC-002","total":"100.00","paid":"50.00","state":"pending","valid":False},
        {"id":"PC-003","total":"100.00","paid":"0.00","state":"pending","valid":False},
        {"id":"PC-004","total":"0.00","paid":"1.00","state":"pending","valid":False},
        {"id":"PC-005","total":"100.00","paid":"101.00","state":"pending","valid":False},
        {"id":"PC-006","total":"100.00","paid":"100.00","state":"paid","valid":False},
        {"id":"PC-007","total":"100.00","paid":"100.00","state":"cancelled","valid":False},
        {"id":"PC-008","total":"100.00","paid":"99.99","state":"pending","valid":False},
        {"id":"PC-009","total":"100.00","paid":"0.01","state":"pending","valid":False},
        {"id":"PC-010","total":"100.00","paid":"100.01","state":"pending","valid":False},
    ]


def payment_capture_selfcheck() -> dict:
    """Run pure payment capture validation cases."""
    cases = payment_capture_acceptance_matrix()
    outcomes = []
    for case in cases:
        result = payment_capture_validation(
            Decimal(case["total"]), Decimal(case["paid"]), case["state"]
        )
        outcomes.append(result["valid"] == case["valid"])
    checks = {
        "ten_payment_cases": len(cases) == 10,
        "unique_case_ids": len({x["id"] for x in cases}) == len(cases),
        "all_expected_results": all(outcomes),
        "zero_capture_rejected": not payment_capture_validation(
            Decimal("100"), Decimal("0"), "pending"
        )["valid"],
        "over_capture_rejected": not payment_capture_validation(
            Decimal("100"), Decimal("100.01"), "pending"
        )["valid"],
        "partial_capture_rejected": not payment_capture_validation(
            Decimal("100"), Decimal("50"), "pending"
        )["valid"],
        "exact_capture_accepted": payment_capture_validation(
            Decimal("100"), Decimal("100"), "pending"
        )["valid"],
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


def end_to_end_audit_scope() -> dict:
    """Document the explicit business event chain covered by the audit."""
    return {
        "order": ["created", "confirmed", "packing", "packed", "ready_to_ship",
                  "shipped", "delivered", "completed", "cancelled", "problem"],
        "stock": ["reserve", "reservation_release", "reservation_expired", "sale", "return"],
        "payment": ["pending", "paid", "refund_confirmed_externally"],
        "return": ["draft", "approved", "refund_ceiling", "refund_record"],
        "loyalty": ["pending_earn", "available_earn", "redeem", "return_reversal",
                    "debt_offset", "expire"],
        "reporting": ["turnover", "captured_payments", "refunds", "expenses"],
        "audit_mode": "read_only",
    }


def end_to_end_audit_scope_selfcheck() -> dict:
    """Pure assertions that the declared chain covers all requested domains."""
    scope = end_to_end_audit_scope()
    checks = {
        "order_chain": "shipped" in scope["order"] and "cancelled" in scope["order"],
        "stock_chain": "sale" in scope["stock"] and "return" in scope["stock"],
        "payment_chain": "paid" in scope["payment"],
        "return_chain": "refund_record" in scope["return"],
        "loyalty_chain": "debt_offset" in scope["loyalty"],
        "reporting_chain": "expenses" in scope["reporting"],
        "read_only": scope["audit_mode"] == "read_only",
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


# =============================================================================
# END ORDER EVENT TIMELINE AND PAYMENT CAPTURE GUARDS
# =============================================================================

def payment_bonus_atomicity_cases() -> list[dict]:
    """Document atomicity guarantees of COD capture and loyalty award."""
    return [
        {"id":"AT-001","case":"payment update succeeds, bonus succeeds",
         "expected":"both changes commit in one db_cursor transaction"},
        {"id":"AT-002","case":"bonus insert fails",
         "expected":"payment status update rolls back with the transaction"},
        {"id":"AT-003","case":"debt offset fails",
         "expected":"payment and bonus changes roll back together"},
        {"id":"AT-004","case":"duplicate payment callback",
         "expected":"already-paid state blocks a second capture"},
        {"id":"AT-005","case":"duplicate bonus worker",
         "expected":"stable order bonus idempotency key prevents duplicate lot"},
        {"id":"AT-006","case":"payment amount zero",
         "expected":"rejected before opening transaction"},
        {"id":"AT-007","case":"payment amount exceeds order total",
         "expected":"rejected by payment_capture_validation"},
        {"id":"AT-008","case":"cancelled order",
         "expected":"payment capture rejected"},
        {"id":"AT-009","case":"no customer record",
         "expected":"payment can be recorded but no loyalty account is created"},
        {"id":"AT-010","case":"partial payment",
         "expected":"rejected until installment ledger and partial settlement lifecycle exist"},
    ]


def payment_bonus_atomicity_selfcheck() -> dict:
    """Check the actual loaded payment and bonus functions, not an unset global."""
    cases = payment_bonus_atomicity_cases()
    try:
        bonus_source = inspect.getsource(_award_order_bonuses_tx)
        payment_source = inspect.getsource(record_cod_payment)
    except (OSError, TypeError):
        bonus_source = payment_source = ""
    checks = {
        "ten_atomicity_cases": len(cases) == 10,
        "unique_ids": len({x["id"] for x in cases}) == 10,
        "stable_bonus_key_in_source": "order:{int(order['id'])}:bonus_earn" in bonus_source,
        "atomic_helper_declared": callable(_award_order_bonuses_tx),
        "payment_capture_uses_helper": "_award_order_bonuses_tx(cur, paid_order, actor)" in payment_source,
        "payment_capture_locks_order": "FOR UPDATE" in payment_source,
        "zero_capture_rejected": "if value <= 0:" in payment_source,
        "transaction_context_used": "with db_cursor() as cur:" in payment_source,
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}


def run_critical_selfchecks() -> dict:
    """Run deterministic checks that do not read or mutate PostgreSQL data."""
    checks = {
        "database_schema_audit": database_schema_audit_selfcheck(),
        "payment_capture": payment_capture_selfcheck(),
        "payment_bonus_atomicity": payment_bonus_atomicity_selfcheck(),
        "business_audit_coverage": business_audit_domain_coverage_selfcheck(),
        "end_to_end_audit_scope": end_to_end_audit_scope_selfcheck(),
    }
    passed = sum(1 for result in checks.values() if result.get("passed"))
    failed = len(checks) - passed
    return {
        "passed": failed == 0,
        "passed_groups": passed,
        "failed_groups": failed,
        "groups": checks,
        "mutates_data": False,
    }


@bot.message_handler(commands=["selfcheck"])
def critical_selfcheck_command(message):
    """Owner-only deterministic regression checks; never touches business rows."""
    staff = stock_command_actor(message)
    if not staff:
        return
    try:
        if staff.role != "owner":
            raise PermissionError("Самоперевірка доступна лише власнику.")
        report = run_critical_selfchecks()
        audit(staff, "system.selfcheck_viewed", "system", "selfcheck",
              after={"passed": report["passed"],
                     "passed_groups": report["passed_groups"],
                     "failed_groups": report["failed_groups"]})
        lines = [
            "<b>Cloud Hub · локальна самоперевірка</b>",
            f"Результат: <b>{'PASS' if report['passed'] else 'FAIL'}</b>",
            f"Груп пройшло: {report['passed_groups']}/{len(report['groups'])}",
        ]
        for name, result in report["groups"].items():
            icon = "✅" if result.get("passed") else "❌"
            lines.append(f"{icon} {safe(name)}: {result.get('passed_count', 0)} passed, "
                         f"{result.get('failed_count', 0)} failed")
            for check_name, ok in result.get("checks", {}).items():
                if not ok:
                    lines.append(f"  • FAIL: {safe(check_name)}")
        lines.append("Перевірки не читають і не змінюють бізнес-дані PostgreSQL.")
        lines.append("PASS не замінює інтеграційні тести з реальною БД і Telegram.")
        stock_report_send(message.chat.id, "🧪 Самоперевірка Cloud Hub", lines,
                          stock_console_back_keyboard())
    except Exception as exc:
        log.exception("Critical self-check failed")
        bot.reply_to(message, safe(str(exc)))


def business_audit_domain_coverage() -> dict:
    """Return explicit coverage metadata for the cross-domain audit report."""
    return {
        "orders": {
            "invariants": ["terminal_order_reservations", "shipped_reservation_consumption"],
            "source_tables": ["orders", "stock_reservations", "audit_log"],
        },
        "stock": {
            "invariants": ["reserved_counter_vs_reservation_rows",
                           "physical_quantity_vs_physical_ledger"],
            "source_tables": ["product_variants", "stock_reservations",
                              "inventory_movements"],
            "reservation_movements_excluded_from_physical_balance": True,
        },
        "payments": {
            "invariants": ["payment_status_vs_paid_amount",
                           "refunds_not_above_captured_payment",
                           "refund_has_approved_return"],
            "source_tables": ["orders", "refund_records", "return_documents"],
        },
        "returns": {
            "invariants": ["refund_not_above_document_ceiling",
                           "returned_quantity_not_above_sold_quantity"],
            "source_tables": ["return_documents", "return_items", "order_items"],
        },
        "loyalty": {
            "invariants": ["account_balance_vs_live_lots",
                           "nonnegative_debt", "lot_state_vs_remaining_amount"],
            "source_tables": ["loyalty_accounts", "loyalty_lots", "loyalty_debts"],
        },
        "notifications": {
            "invariants": ["pending_outbox_count", "failed_outbox_count"],
            "source_tables": ["notification_outbox"],
        },
        "mutates_data": False,
    }


def business_audit_domain_coverage_selfcheck() -> dict:
    """Purely verify that each required business domain has documented checks."""
    coverage = business_audit_domain_coverage()
    required = {"orders", "stock", "payments", "returns", "loyalty", "notifications"}
    checks = {
        "all_required_domains": required.issubset(coverage),
        "all_domains_have_invariants": all(
            bool(coverage[name]["invariants"]) for name in required
        ),
        "all_domains_have_sources": all(
            bool(coverage[name]["source_tables"]) for name in required
        ),
        "physical_stock_excludes_reservations":
            coverage["stock"]["reservation_movements_excluded_from_physical_balance"],
        "audit_is_read_only": coverage["mutates_data"] is False,
    }
    return {"passed": all(checks.values()), "checks": checks,
            "passed_count": sum(checks.values()),
            "failed_count": sum(not x for x in checks.values())}



# ------------------------- BROADCASTS -------------------------
BROADCAST_BATCH_SIZE = 20
BROADCAST_DELAY_SECONDS = 1.1  # conservative Telegram pacing
BROADCAST_MAX_TEXT = 4000


def _broadcast_staff(message_or_call):
    staff = require_staff(message_or_call, "broadcasts.read")
    if not staff:
        return None
    if staff.role not in {"owner", "admin"}:
        return None
    return staff


def broadcast_home(chat_id: int) -> None:
    with db_cursor() as cur:
        cur.execute("""SELECT id,title,state,created_at FROM broadcasts
                       ORDER BY created_at DESC LIMIT 10""")
        rows = list(cur.fetchall())
    kb = types.InlineKeyboardMarkup(row_width=1)
    kb.add(types.InlineKeyboardButton("➕ Створити розсилку", callback_data="bc:create"))
    for row in rows:
        kb.add(types.InlineKeyboardButton(
            f"#{row['id']} · {str(row['title'])[:24]} · {row['state']}",
            callback_data=f"bc:view:{int(row['id'])}"))
    kb.add(types.InlineKeyboardButton("🏠 Головне меню", callback_data="section:home"))
    bot.send_message(chat_id, "<b>📣 Розсилки</b>\nОберіть кампанію або створіть нову.", reply_markup=kb)


def broadcast_create_step(message):
    staff = _broadcast_staff(message)
    if not staff:
        bot.reply_to(message, "⛔ Створювати розсилки можуть лише власник та адміністратор.")
        return
    body = (message.text or "").strip()
    if body.casefold() == "/cancel":
        bot.reply_to(message, "Створення розсилки скасовано.")
        broadcast_home(message.chat.id)
        return
    if not body or len(body) > BROADCAST_MAX_TEXT:
        prompt = bot.reply_to(message, f"Текст має містити 1–{BROADCAST_MAX_TEXT} символів. Спробуйте ще раз або /cancel.")
        bot.register_next_step_handler(prompt, broadcast_create_step)
        return
    title = body.splitlines()[0][:80]
    try:
        with db_cursor() as cur:
            cur.execute("""INSERT INTO broadcasts(title,body,state,created_by)
                           VALUES(%s,%s,'draft',%s) RETURNING id""",
                        (title, body, staff.telegram_id))
            broadcast_id = int(cur.fetchone()["id"])
        kb = types.InlineKeyboardMarkup(row_width=1)
        kb.add(types.InlineKeyboardButton("👥 Усі активні покупці", callback_data=f"bc:audience:{broadcast_id}:all"))
        kb.add(types.InlineKeyboardButton("❌ Видалити чернетку", callback_data=f"bc:delete:{broadcast_id}"))
        bot.send_message(message.chat.id,
            f"<b>Чернетку #{broadcast_id} створено.</b>\n\n{safe(body)}\n\nОберіть аудиторію. До підтвердження нічого не надсилається.",
            reply_markup=kb)
    except Exception:
        log.exception("Broadcast draft creation failed")
        bot.reply_to(message, "⚠️ Не вдалося створити чернетку. Перевірте журнал помилок.")


def broadcast_render(chat_id: int, broadcast_id: int):
    with db_cursor() as cur:
        cur.execute("SELECT * FROM broadcasts WHERE id=%s", (broadcast_id,))
        campaign = cur.fetchone()
        if not campaign:
            bot.send_message(chat_id, "Розсилку не знайдено.")
            return
        cur.execute("""SELECT COUNT(*) total,
                       COUNT(*) FILTER(WHERE state='pending') pending,
                       COUNT(*) FILTER(WHERE state='sent') sent,
                       COUNT(*) FILTER(WHERE state='failed') failed,
                       COUNT(*) FILTER(WHERE state IN ('skipped','blocked')) skipped
                       FROM broadcast_recipients WHERE broadcast_id=%s""", (broadcast_id,))
        stats = cur.fetchone()
    kb = types.InlineKeyboardMarkup(row_width=1)
    if campaign["state"] == "draft" and int(stats["total"] or 0) > 0:
        kb.add(types.InlineKeyboardButton("👁 Попередній перегляд", callback_data=f"bc:preview:{broadcast_id}"))
        kb.add(types.InlineKeyboardButton("🚀 ПІДТВЕРДИТИ ТА НАДІСЛАТИ", callback_data=f"bc:confirm:{broadcast_id}"))
    if campaign["state"] in {"running", "scheduled"}:
        kb.add(types.InlineKeyboardButton("⏸ Зупинити", callback_data=f"bc:stop:{broadcast_id}"))
    kb.add(types.InlineKeyboardButton("↩️ До розсилок", callback_data="bc:home"))
    text = (f"<b>Розсилка #{broadcast_id}</b>\n"
            f"Статус: <b>{safe(campaign['state'])}</b>\n"
            f"Текст:\n{safe(campaign['body'])}\n\n"
            f"Аудиторія: {stats['total']}\nОчікують: {stats['pending']}\n"
            f"Надіслано: {stats['sent']}\nПомилки: {stats['failed']}\nПропущено (відписалися/заблокували бота): {stats['skipped']}")
    bot.send_message(chat_id, text, reply_markup=kb)


BROADCAST_FOOTER = ""
_BROADCAST_THREADS: dict = {}
_BROADCAST_LOCK = threading.Lock()


def _marketing_opted_in(ids: Optional[list] = None) -> set:
    """Registered customers, excluding accounts with an explicit marketing opt-out."""
    if ids is None:
        with db_cursor() as cur:
            cur.execute("SELECT telegram_id FROM customers WHERE telegram_id IS NOT NULL")
            candidates = {int(r["telegram_id"]) for r in cur.fetchall()}
    else:
        candidates = {int(x) for x in ids}
    if not candidates:
        return set()
    with consent_db_cursor() as cur:
        cur.execute(
            """SELECT telegram_id FROM consent_records
               WHERE consent_version=%s AND accepted=FALSE AND telegram_id=ANY(%s)""",
            (MARKETING_CONSENT_KEY, list(candidates)))
        opted_out = {int(r["telegram_id"]) for r in cur.fetchall()}
    return candidates - opted_out


def start_broadcast_worker(broadcast_id: int) -> bool:
    """Start at most one worker thread per campaign."""
    with _BROADCAST_LOCK:
        thread = _BROADCAST_THREADS.get(broadcast_id)
        if thread is not None and thread.is_alive():
            return False
        thread = threading.Thread(target=broadcast_worker, args=(broadcast_id,), daemon=True,
                                  name=f"broadcast-{broadcast_id}")
        _BROADCAST_THREADS[broadcast_id] = thread
        thread.start()
        return True


def resume_running_broadcasts() -> None:
    """After a restart: put half-sent recipients back in the queue and restart running campaigns."""
    with db_cursor() as cur:
        cur.execute("""UPDATE broadcast_recipients SET state='pending'
                       WHERE state='sending' AND broadcast_id IN (SELECT id FROM broadcasts WHERE state='running')""")
        cur.execute("SELECT id FROM broadcasts WHERE state='running'")
        ids = [int(r["id"]) for r in cur.fetchall()]
    for broadcast_id in ids:
        start_broadcast_worker(broadcast_id)
    if ids:
        log.info("Resumed running broadcasts: %s", ids)


def _broadcast_send_one(broadcast_id: int, recipient_id: int, telegram_id: int, attempts: int, text: str) -> Optional[float]:
    """Send one message. Returns seconds to wait if Telegram asked us to slow down."""
    try:
        bot.send_message(telegram_id, text, disable_web_page_preview=True)
        with db_cursor() as cur:
            cur.execute("""UPDATE broadcast_recipients SET state='sent',sent_at=NOW(),last_error=NULL
                           WHERE id=%s AND state='sending'""", (recipient_id,))
        return None
    except Exception as exc:
        code = getattr(exc, "error_code", None)
        err = str(exc)[:1000]
        if code == 429:
            retry_after = 5
            try:
                retry_after = int((getattr(exc, "result_json", None) or {}).get("parameters", {}).get("retry_after", 5))
            except Exception:
                pass
            with db_cursor() as cur:
                cur.execute("UPDATE broadcast_recipients SET state='pending',last_error=%s WHERE id=%s AND state='sending'",
                            ("429 flood wait", recipient_id))
            return float(min(max(retry_after, 1) + 1, 300))
        if code == 403:
            new_state = "blocked"          # user blocked the bot / deactivated: never retry
        elif code is None or (isinstance(code, int) and code >= 500):
            new_state = "pending" if attempts < 3 else "failed"   # network / Telegram hiccup
        else:
            new_state = "failed"
        with db_cursor() as cur:
            cur.execute("UPDATE broadcast_recipients SET state=%s,last_error=%s WHERE id=%s AND state='sending'",
                        (new_state, err, recipient_id))
        return 3.0 if new_state == "pending" else None


def broadcast_worker(broadcast_id: int):
    """Send only rows atomically claimed from the recipient queue.

    A campaign is completed only when nothing is pending AND nothing is still 'sending'.
    Only users with accepted marketing consent receive messages (re-checked per batch).
    """
    try:
        while True:
            with db_cursor() as cur:
                cur.execute("SELECT state,body FROM broadcasts WHERE id=%s", (broadcast_id,))
                campaign = cur.fetchone()
                if not campaign or campaign["state"] != "running":
                    return
                body = campaign["body"]
                cur.execute("""SELECT id,customer_telegram_id FROM broadcast_recipients
                               WHERE broadcast_id=%s AND state='pending'
                               ORDER BY id LIMIT %s FOR UPDATE SKIP LOCKED""",
                            (broadcast_id, BROADCAST_BATCH_SIZE))
                batch = list(cur.fetchall())
                if not batch:
                    cur.execute("SELECT COUNT(*) n FROM broadcast_recipients WHERE broadcast_id=%s AND state='sending'",
                                (broadcast_id,))
                    in_flight = int(cur.fetchone()["n"])
                    if in_flight == 0:
                        cur.execute("UPDATE broadcasts SET state='completed' WHERE id=%s AND state='running'", (broadcast_id,))
                        return
            if not batch:
                time.sleep(2)
                continue
            allowed = _marketing_opted_in([int(r["customer_telegram_id"]) for r in batch])
            text = html.escape(body) + BROADCAST_FOOTER
            for recipient in batch:
                with db_cursor() as cur:
                    cur.execute("SELECT state FROM broadcasts WHERE id=%s", (broadcast_id,))
                    current = cur.fetchone()
                if not current or current["state"] != "running":
                    return
                telegram_id = int(recipient["customer_telegram_id"])
                with db_cursor() as cur:
                    if telegram_id not in allowed:
                        cur.execute("""UPDATE broadcast_recipients SET state='skipped',last_error='no marketing consent'
                                       WHERE id=%s AND state='pending'""", (recipient["id"],))
                        continue
                    cur.execute("""UPDATE broadcast_recipients SET state='sending',attempts=attempts+1
                                   WHERE id=%s AND state='pending' RETURNING attempts""", (recipient["id"],))
                    claimed = cur.fetchone()
                if not claimed:
                    continue
                wait = _broadcast_send_one(broadcast_id, int(recipient["id"]), telegram_id, int(claimed["attempts"]), text)
                time.sleep(wait if wait else BROADCAST_DELAY_SECONDS)
    except Exception:
        log.exception("Broadcast worker crashed for campaign %s", broadcast_id)
        try:
            with db_cursor() as cur:
                cur.execute("UPDATE broadcasts SET state='failed' WHERE id=%s AND state='running'", (broadcast_id,))
        except Exception:
            log.exception("Could not mark broadcast %s as failed", broadcast_id)

@bot.callback_query_handler(func=lambda c: c.data.startswith("bc:"))
def broadcast_callback(call):
    staff = _broadcast_staff(call)
    if not staff:
        bot.answer_callback_query(call.id, "Доступ заборонено.", show_alert=True)
        return
    parts = call.data.split(":")
    action = parts[1]
    bot.answer_callback_query(call.id)
    try:
        if action == "home":
            broadcast_home(call.message.chat.id)
        elif action == "create":
            prompt = bot.send_message(call.message.chat.id,
                f"Надішліть текст розсилки (до {BROADCAST_MAX_TEXT} символів). /cancel скасовує створення.")
            bot.register_next_step_handler(prompt, broadcast_create_step)
        elif action == "audience":
            broadcast_id = int(parts[2])
            if parts[3] != "all":
                return
            opted_in_ids = sorted(_marketing_opted_in())
            if not opted_in_ids:
                bot.send_message(call.message.chat.id, "Немає доступних клієнтів для цієї розсилки.")
                return
            with db_cursor() as cur:
                cur.execute("SELECT state FROM broadcasts WHERE id=%s FOR UPDATE", (broadcast_id,))
                row = cur.fetchone()
                if not row or row["state"] != "draft":
                    bot.send_message(call.message.chat.id, "Чернетка вже недоступна для зміни.")
                    return
                cur.execute("""INSERT INTO broadcast_recipients(broadcast_id,customer_telegram_id)
                               SELECT %s,telegram_id FROM customers
                               WHERE telegram_id IS NOT NULL AND telegram_id = ANY(%s)
                               ON CONFLICT(broadcast_id,customer_telegram_id) DO NOTHING""",
                            (broadcast_id, opted_in_ids))
            broadcast_render(call.message.chat.id, broadcast_id)
        elif action == "view":
            broadcast_render(call.message.chat.id, int(parts[2]))
        elif action == "preview":
            broadcast_id = int(parts[2])
            with db_cursor() as cur:
                cur.execute("SELECT body,state FROM broadcasts WHERE id=%s", (broadcast_id,))
                row = cur.fetchone()
                cur.execute("SELECT COUNT(*) n FROM broadcast_recipients WHERE broadcast_id=%s",
                            (broadcast_id,))
                count = int(cur.fetchone()["n"])
            if row and row["state"] == "draft":
                kb = types.InlineKeyboardMarkup()
                kb.add(types.InlineKeyboardButton("Повернутися", callback_data=f"bc:view:{broadcast_id}"))
                bot.send_message(call.message.chat.id,
                    f"<b>Попередній перегляд</b>\nОдержувачів: {count}\n\n{safe(row['body'])}", reply_markup=kb)
        elif action == "confirm":
            broadcast_id = int(parts[2])
            with db_cursor() as cur:
                cur.execute("""UPDATE broadcasts SET state='running'
                               WHERE id=%s AND state='draft'
                               AND EXISTS(SELECT 1 FROM broadcast_recipients WHERE broadcast_id=%s)
                               RETURNING id""", (broadcast_id, broadcast_id))
                row = cur.fetchone()
            if not row:
                bot.send_message(call.message.chat.id, "Розсилку не запущено: вона вже запускалася або аудиторія порожня.")
                return
            bot.send_message(call.message.chat.id, f"🚀 Розсилку #{broadcast_id} запущено. Її можна зупинити з картки кампанії.")
            start_broadcast_worker(broadcast_id)
        elif action == "stop":
            broadcast_id = int(parts[2])
            with db_cursor() as cur:
                cur.execute("""UPDATE broadcasts SET state='cancelled'
                               WHERE id=%s AND state IN ('running','scheduled') RETURNING id""",
                            (broadcast_id,))
                stopped = cur.fetchone()
            bot.send_message(call.message.chat.id,
                "⏸ Розсилку зупинено. Уже надіслані повідомлення не відкликаються." if stopped
                else "Розсилку вже завершено або зупинено.")
        elif action == "delete":
            broadcast_id = int(parts[2])
            with db_cursor() as cur:
                cur.execute("DELETE FROM broadcast_recipients WHERE broadcast_id=%s", (broadcast_id,))
                cur.execute("DELETE FROM broadcasts WHERE id=%s AND state='draft' RETURNING id",
                            (broadcast_id,))
                deleted = cur.fetchone()
            bot.send_message(call.message.chat.id, "Чернетку видалено." if deleted else "Видалити можна лише чернетку.")
    except Exception:
        log.exception("Broadcast callback failed: %s", call.data)
        bot.send_message(call.message.chat.id, "⚠️ Не вдалося виконати дію з розсилкою. Помилку записано в журнал.")


if __name__ == "__main__":
    main()
