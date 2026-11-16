# Cloud Hub

Telegram commerce bot and Mini App backed by PostgreSQL.

The single-file application is `Cloud_Hub_v1_55_audit_fixes-1.py`. The Render worker runs this file directly. The Mini App web service loads it with `runpy.run_path(...)` because the filename contains a hyphen.

## Customer Mini App

- Browse the shared CRM catalogue, save favorites, and place orders.
- Use available bonuses up to the full item total and redeem gift certificates.
- Share a referral link; after the friend's first delivered order, each customer receives 50 bonuses.
- Review order history and delivery tracking status.

## Owner tools

The owner dashboard shows sales and order summaries, customers, pending orders, loyalty liability, certificates, and referral rewards. The owner can adjust customer bonuses with an audit trail and issue gift certificates.

## Staff workspace

Active staff with the required role permissions can use the Mini App workspace to create and edit products, change names, descriptions, SKUs, and prices, adjust inventory, upload product photos, search orders and update their status, and view customer cards with order history and loyalty transactions. Role assignment and staff account lifecycle remain in the Telegram bot owner tools.

## Run configuration

Required environment variables include `BOT_TOKEN`, `DATABASE_URL`, `OWNER_TELEGRAM_ID`, and privacy consent settings. Nova Poshta API operations require `NOVA_POSHTA_API_KEY` and the sender references described in the application file. Customers can enter city and branch manually if the directory is unavailable.

Run the worker with:

```bash
python Cloud_Hub_v1_55_audit_fixes-1.py
```

The Mini App service must load the same file through `runpy.run_path(...)`. Live Telegram, database, checkout, and Nova Poshta acceptance checks are required before production rollout.
