#!/usr/bin/env python3
"""Сборщик VLESS+Reality серверов с SNI под российские домены (для «белых списков»).

Откуда берёт (см. sources.txt):
  search: — поиск по коду на GitHub (нужен токен, в Actions есть GITHUB_TOKEN)
  repo:   — все текстовые файлы репозитория
  url:    — прямая ссылка на список / подписку
  tg:     — публичный Telegram-канал (веб-превью t.me/s/<канал>)

Что делает:
  1. достаёт vless://, оставляет только Reality с SNI под российские домены, убирает дубли;
  2. TCP-проверка (отсев мёртвых + задержка);
  3. реальный тест скорости через Xray (скачивание файла через сам сервер);
  4. сортировка по скорости, не больше 2 серверов на один IP, не больше 450 всего;
  5. страна и город определяются по IP, имя: «🇩🇪 Германия, Франкфурт».

Результат (папка out/):
  whitelist_ru_sni.txt        — список ссылок, самые быстрые сверху
  whitelist_ru_sni_b64.txt    — то же, base64-подпиской
  whitelist_ru_sni_ruip.txt   — только серверы, физически находящиеся в РФ

Только стандартная библиотека Python 3.9+ (для теста скорости нужны xray и curl).
"""
import argparse
import base64
import concurrent.futures as cf
import html
import ipaddress
import itertools
import json
import os
import re
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse as up
import urllib.request as ur
from collections import Counter
from datetime import datetime, timedelta, timezone
from pathlib import Path

ROOT = Path(__file__).parent
OUT = ROOT / "out"
SOURCES_FILE = ROOT / "sources.txt"

# ───────────────────────────── НАСТРОЙКИ ─────────────────────────────
# Домены маскировки. Совпадение — точное или по поддомену (api.vk.com тоже подойдёт).
TIER1 = [  # то, что просили в первую очередь: VK, Яндекс, Max, Ozon
    "vk.com", "vk.ru", "vkvideo.ru", "userapi.com", "vkuser.net",
    "yandex.ru", "yandex.com", "yandex.net", "ya.ru", "yastatic.net", "yandexcloud.net",
    "max.ru", "oneme.ru",
    "ozon.ru", "ozone.ru",
]
TIER2 = [  # прочие российские сервисы, которые обычно в белых списках
    "ok.ru", "mail.ru", "mycdn.me", "dzen.ru", "kinopoisk.ru", "rutube.ru",
    "wildberries.ru", "wb.ru", "sber.ru", "sberbank.ru", "tbank.ru", "tinkoff.ru",
    "gosuslugi.ru", "mos.ru", "avito.ru", "2gis.ru", "2gis.com",
    "mts.ru", "megafon.ru", "beeline.ru", "rzd.ru",
]

# Транспорты. xhttp не берём: ядро sing-box (Karing) его не поддерживает.
ALLOWED_TYPES = {"tcp", "grpc"}

MAX_TOTAL = 450         # итоговый размер списка
MAX_PER_IP = 2          # не больше стольких серверов на один IP
MAX_TEST = 1500         # сколько кандидатов максимум гонять через тест скорости
SPEED_WORKERS = 16      # сколько Xray запускать параллельно
SPEED_URL = "https://speed.cloudflare.com/__down?bytes=2000000"
SPEED_BYTES = 2_000_000
SPEED_TIMEOUT = 12      # секунд на скачивание
TG_PAGES = 5            # страниц истории у каждого канала (~20 постов на страницу)
TG_MAX_AGE_DAYS = 14    # старые посты пропускаем
GH_SEARCH_PAGES = 2     # страниц выдачи на каждый поисковый запрос (по 100 файлов)
GH_MAX_FILES_PER_REPO = 60
GEO_LANG = "ru"         # язык названий стран/городов
# ─────────────────────────────────────────────────────────────────────

UA = "Mozilla/5.0 (compatible; reality-collector/1.0)"
VLESS_RE = re.compile(r"vless://[^\s<>\"'`]+")
UUID_RE = re.compile(r"^[0-9a-fA-F]{8}-(?:[0-9a-fA-F]{4}-){3}[0-9a-fA-F]{12}$")
PBK_RE = re.compile(r"^[A-Za-z0-9_-]{43}$")
SID_RE = re.compile(r"^(?:[0-9a-fA-F]{2}){0,8}$")
TEXT_EXT = {"", ".txt", ".md", ".json", ".yaml", ".yml", ".conf", ".sub", ".list"}
_ports = itertools.count(20000)


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ───────────────────────────── сеть ─────────────────────────────
def http(url, headers=None, data=None, timeout=25, max_bytes=8_000_000, retries=2):
    h = {"User-Agent": UA}
    h.update(headers or {})
    for i in range(retries + 1):
        try:
            req = ur.Request(url, data=data, headers=h)
            with ur.urlopen(req, timeout=timeout) as r:
                return r.read(max_bytes).decode("utf-8", "ignore")
        except urllib.error.HTTPError as e:
            if e.code in (404, 410, 451):
                return None
            if e.code in (403, 429) and "api.github.com" in url:
                log(f"  ! GitHub API {e.code}, жду 30 с")
                time.sleep(30)
        except Exception:
            pass
        time.sleep(1.5 * (i + 1))
    return None


def gh_api(url, token):
    h = {"Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"}
    if token:
        h["Authorization"] = f"Bearer {token}"
    txt = http(url, headers=h)
    try:
        return json.loads(txt) if txt else None
    except ValueError:
        return None


# ───────────────────────── разбор ссылок ─────────────────────────
def match_tier(sni):
    s = sni.lower().rstrip(".")
    for tier, domains in ((1, TIER1), (2, TIER2)):
        for d in domains:
            if s == d or s.endswith("." + d):
                return tier
    return 0


def try_b64(text):
    s = re.sub(r"\s+", "", text)
    if len(s) < 40 or not re.fullmatch(r"[A-Za-z0-9+/_=-]+", s):
        return ""
    s = s.replace("-", "+").replace("_", "/")
    s += "=" * (-len(s) % 4)
    try:
        return base64.b64decode(s).decode("utf-8", "ignore")
    except Exception:
        return ""


def extract_links(text, unescape_html=False):
    text = html.unescape(text) if unescape_html else text.replace("&amp;", "&")
    if "vless://" not in text:
        text = try_b64(text) or text
    return [m.rstrip(".,;)]}»") for m in VLESS_RE.findall(text)]


def public_host(host):
    if not host:
        return False
    try:
        ip = ipaddress.ip_address(host)
        return not (ip.is_private or ip.is_loopback or ip.is_link_local
                    or ip.is_multicast or ip.is_unspecified or ip.is_reserved)
    except ValueError:
        return "." in host and host != "localhost" and not host.endswith(".local")


def parse_vless(link, keep_other=False):
    """Возвращает dict или None, если ссылка не подходит."""
    try:
        u = up.urlsplit(link)
        port = u.port
        host = u.hostname
    except ValueError:
        return None
    if u.scheme != "vless" or not u.username or not port or not public_host(host):
        return None
    if not UUID_RE.match(u.username):
        return None
    q = {k.lower(): v for k, v in up.parse_qsl(u.query, keep_blank_values=True)}
    if q.get("security", "").lower() != "reality":
        return None
    if q.get("encryption", "none").lower() not in ("none", ""):
        return None  # новое VLESS-шифрование (ML-KEM) клиенты почти не понимают
    if (q.get("type") or "tcp").lower() not in ALLOWED_TYPES:
        return None
    if not PBK_RE.match(q.get("pbk", "")) or not SID_RE.match(q.get("sid", "")):
        return None
    sni = (q.get("sni") or q.get("servername") or "").strip().lower()
    if not sni:
        return None
    tier = match_tier(sni)
    if tier == 0 and not keep_other:
        return None
    return {
        "base": link.split("#", 1)[0], "q": q,
        "host": host.lower(), "port": port, "uuid": u.username.lower(),
        "sni": sni, "tier": tier,
    }


# ───────────────────────────── источники ─────────────────────────────
def load_sources():
    src = {"search": [], "repo": [], "url": [], "tg": []}
    if SOURCES_FILE.exists():
        for line in SOURCES_FILE.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#") or ":" not in line:
                continue
            kind, val = line.split(":", 1)
            kind, val = kind.strip().lower(), val.strip()
            if kind in src and val:
                src[kind].append(val)
    if not src["search"]:  # запросы по умолчанию — из основных доменов
        for d in ("vk.com", "vk.ru", "yandex.ru", "ya.ru", "max.ru", "ozon.ru", "userapi.com"):
            src["search"].append(f'"security=reality" "sni={d}"')
    return src


def to_raw(html_url):
    m = re.match(r"^https://github\.com/([^/]+/[^/]+)/blob/([^/]+)/(.+)$", html_url)
    return f"https://raw.githubusercontent.com/{m.group(1)}/{m.group(2)}/{m.group(3)}" if m else None


def gh_search_files(queries, token):
    """Поиск по коду. Лимит у GitHub — 10 запросов в минуту, поэтому пауза 7 с."""
    urls = []
    for q in queries:
        for page in range(1, GH_SEARCH_PAGES + 1):
            data = gh_api("https://api.github.com/search/code?per_page=100&page=%d&q=%s"
                          % (page, up.quote(q)), token)
            time.sleep(7)
            items = (data or {}).get("items") or []
            urls += [r for r in (to_raw(i.get("html_url", "")) for i in items) if r]
            if len(items) < 100:
                break
        log(f"  search {q[:60]} → всего файлов {len(set(urls))}")
    return list(dict.fromkeys(urls))


def repo_file_urls(repo, token):
    data = gh_api(f"https://api.github.com/repos/{repo}/git/trees/HEAD?recursive=1", token)
    files = []
    for t in (data or {}).get("tree", []):
        if t.get("type") != "blob" or t.get("size", 0) > 4_000_000:
            continue
        if os.path.splitext(t["path"])[1].lower() in TEXT_EXT:
            files.append(t["path"])
    key = lambda p: (not re.search(r"reality|vless|white|sni|ru", p, re.I), p)
    files = sorted(files, key=key)[:GH_MAX_FILES_PER_REPO]
    return [f"https://raw.githubusercontent.com/{repo}/HEAD/{up.quote(p)}" for p in files]


def fetch_tg(channel):
    channel = re.sub(r"^(https?://)?(t\.me/(s/)?)?@?", "", channel.strip()).strip("/")
    if not re.fullmatch(r"[A-Za-z0-9_]{4,64}", channel):
        log(f"  ! странное имя канала: {channel}")
        return []
    cutoff = datetime.now(timezone.utc) - timedelta(days=TG_MAX_AGE_DAYS)
    links, before = [], None
    for _ in range(TG_PAGES):
        page = http(f"https://t.me/s/{channel}" + (f"?before={before}" if before else ""))
        chunks = (page or "").split('data-post="')[1:]
        ids, oldest = [], None
        for ch in chunks:
            m = re.match(r"[\w]+/(\d+)", ch)
            if not m:
                continue
            ids.append(int(m.group(1)))
            tm = re.search(r'<time[^>]*datetime="([^"]+)"', ch)
            try:
                ts = datetime.fromisoformat(tm.group(1)) if tm else None
            except ValueError:
                ts = None
            if ts:
                oldest = ts if oldest is None else min(oldest, ts)
            if ts is None or ts >= cutoff:
                links += extract_links(ch, unescape_html=True)
        if not ids or (oldest and oldest < cutoff):
            break
        before = min(ids)
        time.sleep(1)
    return links


# ───────────────────── проверка, скорость, гео ─────────────────────
def resolve(host):
    try:
        return socket.getaddrinfo(host, None, proto=socket.IPPROTO_TCP)[0][4][0]
    except OSError:
        return None


def tcp_ping(c, timeout=4):
    """Задержка TCP-подключения в мс или None, если порт закрыт."""
    t = time.monotonic()
    try:
        with socket.create_connection((c["host"], c["port"]), timeout=timeout):
            return (time.monotonic() - t) * 1000
    except OSError:
        return None


def xray_config(c, port):
    q = c["q"]
    grpc = (q.get("type") or "tcp").lower() == "grpc"
    user = {"id": c["uuid"], "encryption": "none"}
    if q.get("flow") and not grpc:
        user["flow"] = q["flow"]
    ss = {"security": "reality", "realitySettings": {
        "serverName": c["sni"], "fingerprint": q.get("fp") or "chrome",
        "publicKey": q["pbk"], "shortId": q.get("sid", ""), "spiderX": q.get("spx", "")}}
    if grpc:
        ss["network"] = "grpc"
        ss["grpcSettings"] = {"serviceName": q.get("servicename", ""), "multiMode": q.get("mode") == "multi"}
    else:
        ss["network"] = "tcp"
    return {
        "log": {"loglevel": "none"},
        "inbounds": [{"listen": "127.0.0.1", "port": port, "protocol": "socks", "settings": {"udp": False}}],
        "outbounds": [{"protocol": "vless", "streamSettings": ss,
                       "settings": {"vnext": [{"address": c["host"], "port": c["port"], "users": [user]}]}}],
    }


def speed_test(c, xray_bin):
    """Скачивает SPEED_URL через сервер. Возвращает Мбит/с или None, если сервер не работает."""
    port = next(_ports)
    p = None
    with tempfile.TemporaryDirectory() as d:
        cfg = Path(d) / "c.json"
        cfg.write_text(json.dumps(xray_config(c, port)))
        try:
            p = subprocess.Popen([xray_bin, "run", "-c", str(cfg)],
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            for _ in range(40):  # ждём, пока Xray откроет порт (до 4 с)
                if p.poll() is not None:
                    return None
                try:
                    socket.create_connection(("127.0.0.1", port), 0.2).close()
                    break
                except OSError:
                    time.sleep(0.1)
            else:
                return None
            r = subprocess.run(
                ["curl", "-s", "-o", "/dev/null", "-m", str(SPEED_TIMEOUT),
                 "-x", f"socks5h://127.0.0.1:{port}",
                 "-w", "%{http_code} %{size_download} %{speed_download}", SPEED_URL],
                capture_output=True, text=True, timeout=SPEED_TIMEOUT + 5)
            code, size, speed = r.stdout.split()
            if code != "200" or float(size) < SPEED_BYTES * 0.9:
                return None
            return float(speed) * 8 / 1e6
        except (subprocess.TimeoutExpired, ValueError, OSError):
            return None
        finally:
            if p:
                p.kill()
                p.wait()


def geo_lookup(ips):
    """ip-api.com, пакеты по 100 (лимит бесплатного тарифа — 15 пакетов в минуту)."""
    res, ips = {}, list(ips)
    for i in range(0, len(ips), 100):
        body = json.dumps([{"query": ip, "fields": "status,country,countryCode,city,query",
                            "lang": GEO_LANG} for ip in ips[i:i + 100]]).encode()
        txt = http("http://ip-api.com/batch", headers={"Content-Type": "application/json"}, data=body)
        try:
            for r in json.loads(txt or "[]"):
                if r.get("status") == "success":
                    res[r["query"]] = r
        except ValueError:
            pass
        time.sleep(4.5)
    return res


def flag(cc):
    if not re.fullmatch(r"[A-Za-z]{2}", cc or ""):
        return "🏳"
    return "".join(chr(0x1F1E6 + ord(c) - 65) for c in cc.upper())


def build(raw, keep_other=False, check_tcp=True, xray_bin=None, use_geo=True,
          resolver=resolve, tcp_fn=tcp_ping, speed_fn=speed_test, geo_fn=geo_lookup):
    stats = Counter(found=len(raw))

    # 1. разбор и дедупликация
    cands = {}
    for link in raw:
        c = parse_vless(link, keep_other)
        if not c:
            continue
        key = (c["host"], c["port"], c["uuid"])
        if key not in cands or (c["tier"] and (not cands[key]["tier"] or c["tier"] < cands[key]["tier"])):
            cands[key] = c
    cands = list(cands.values())
    stats["reality_ru_sni"] = len(cands)

    # 2. DNS → IP
    hosts = sorted({c["host"] for c in cands})
    with cf.ThreadPoolExecutor(64) as ex:
        ip_of = dict(zip(hosts, ex.map(resolver, hosts)))
    cands = [c for c in cands if ip_of.get(c["host"])]
    for c in cands:
        c["ip"] = ip_of[c["host"]]

    # 3. TCP: отсев мёртвых и задержка
    if check_tcp:
        with cf.ThreadPoolExecutor(100) as ex:
            pings = list(ex.map(tcp_fn, cands))
        cands = [dict(c, ms=ms) for c, ms in zip(cands, pings) if ms is not None]
        stats["tcp_ok"] = len(cands)
    for c in cands:
        c.setdefault("ms", 0.0)

    # 4. реальный тест скорости через Xray
    rank = lambda c: (c["tier"] == 0, -c.get("mbps", 0.0), c["ms"], c["base"])
    cands.sort(key=lambda c: (c["tier"] == 0, c["ms"], c["base"]))
    if xray_bin:
        batch = cands[:MAX_TEST]
        log(f"Тест скорости: {len(batch)} серверов, {SPEED_WORKERS} параллельно…")
        with cf.ThreadPoolExecutor(SPEED_WORKERS) as ex:
            res = list(ex.map(lambda c: speed_fn(c, xray_bin), batch))
        cands = [dict(c, mbps=s) for c, s in zip(batch, res) if s]
        stats["speed_ok"] = len(cands)
    cands.sort(key=rank)

    # 5. лимит на IP и общий потолок
    per_ip, final = Counter(), []
    for c in cands:
        if per_ip[c["ip"]] >= MAX_PER_IP:
            continue
        per_ip[c["ip"]] += 1
        final.append(c)
        if len(final) >= MAX_TOTAL:
            break

    # 6. страна и город по IP (только для тех, кто попал в итог)
    geo = geo_fn({c["ip"] for c in final}) if use_geo and final else {}
    for c in final:
        g = geo.get(c["ip"], {})
        c["cc"] = g.get("countryCode", "")
        country, city = g.get("country", ""), g.get("city", "")
        c["name"] = (f"{flag(c['cc'])} {country}" + (f", {city}" if city and city != country else "")
                     ) if country else "🏳 Неизвестно"
    stats["final"] = len(final)
    stats["final_ru_ip"] = sum(c["cc"] == "RU" for c in final)
    return final, stats


def write_outputs(final):
    OUT.mkdir(exist_ok=True)
    line = lambda c: f"{c['base']}#{up.quote(c['name'])}"
    allp = "\n".join(line(c) for c in final) + "\n"
    (OUT / "whitelist_ru_sni.txt").write_text(allp, encoding="utf-8")
    (OUT / "whitelist_ru_sni_b64.txt").write_text(base64.b64encode(allp.encode()).decode(), encoding="utf-8")
    ru = "\n".join(line(c) for c in final if c["cc"] == "RU")
    (OUT / "whitelist_ru_sni_ruip.txt").write_text(ru + "\n" if ru else "", encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--xray", help="путь к бинарнику xray (или переменная XRAY_BIN); без него скорость не мерим, сортировка по TCP-задержке")
    ap.add_argument("--no-speed", action="store_true", help="не запускать тест скорости")
    ap.add_argument("--no-tcp", action="store_true", help="не делать TCP-проверку")
    ap.add_argument("--no-geo", action="store_true", help="не определять страну по IP")
    ap.add_argument("--keep-other", action="store_true", help="добирать Reality и с нероссийским SNI (в конец списка)")
    ap.add_argument("--skip-github-search", action="store_true")
    args = ap.parse_args()

    xray_bin = None
    if not args.no_speed:
        cand = args.xray or os.environ.get("XRAY_BIN") or "xray"
        found = shutil.which(cand)
        if not found:
            log("! xray не найден — скорость не измеряю, сортирую по TCP-задержке")
        elif not shutil.which("curl"):
            log("! curl не найден — скорость не измеряю, сортирую по TCP-задержке")
        else:
            xray_bin = str(Path(found).resolve())

    token = os.environ.get("GH_SEARCH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    src = load_sources()
    urls = list(src["url"])
    raw = []

    for repo in src["repo"]:
        found = repo_file_urls(repo, token)
        log(f"repo {repo}: файлов {len(found)}")
        urls += found
    if src["search"] and not args.skip_github_search:
        if not token:
            log("! нет GITHUB_TOKEN — поиск по коду GitHub пропущен")
        else:
            urls += gh_search_files(src["search"], token)

    urls = list(dict.fromkeys(urls))
    log(f"Скачиваю {len(urls)} файлов…")
    with cf.ThreadPoolExecutor(8) as ex:
        for txt in ex.map(http, urls):
            if txt:
                raw += extract_links(txt)

    for ch in src["tg"]:
        got = fetch_tg(ch)
        log(f"tg {ch}: ссылок {len(got)}")
        raw += got

    final, stats = build(raw, args.keep_other, not args.no_tcp, xray_bin, not args.no_geo)
    write_outputs(final)
    log("Итого:", dict(stats))
    if not final:
        log("! ничего не найдено — файлы перезаписаны пустыми, проверь sources.txt")


if __name__ == "__main__":
    main()
