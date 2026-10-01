#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Niche Radar — поиск зарождающихся ниш на YouTube.

Логика «снизу вверх» (без заранее заданного списка тем):
  1. Собираем свежие видео (тренды по категориям + широкие поисковые запросы).
  2. Находим аномалии: маленькие каналы с непропорционально большими просмотрами.
  3. Из названий и тегов таких видео автоматически выделяем темы
     и группируем их: если на одну тему одновременно «выстрелили»
     несколько разных маленьких каналов — это кандидат в новую нишу.
  4. Сравниваем с прошлыми запусками (history.json), чтобы видеть рост.

Только стандартная библиотека Python 3.8+, ничего устанавливать не нужно.

Запуск:
  python niche_radar.py --key ВАШ_API_КЛЮЧ
  python niche_radar.py --demo          (проверка на тестовых данных, без ключа)
"""

import argparse
import csv
import datetime as dt
import html
import json
import math
import os
import random
import re
import statistics
import sys
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict

# ════════════════════════════════════════════════════════════════════
# НАСТРОЙКИ — меняйте под себя
# ════════════════════════════════════════════════════════════════════
CONFIG = {
    # Страны, по которым сканируем (коды ISO): US, GB, RU, PL, DE, IN, BR ...
    "regions": ["US", "PL", "DE", "RU"],

    # Сколько дней назад смотрим (свежесть видео)
    "days_back": 7,

    # Категории YouTube для раздела «В тренде» (дёшево по квоте: 1 ед. за запрос)
    # 1 Фильмы, 2 Авто, 10 Музыка, 15 Животные, 17 Спорт, 20 Игры,
    # 22 Блоги, 23 Юмор, 24 Развлечения, 25 Новости, 26 Хобби/How-to,
    # 27 Образование, 28 Наука и техника
    "trend_categories": ["0", "1", "2", "15", "17", "20", "22", "23", "24", "26", "27", "28"],

    # Широкие «затравки» для поиска. Это НЕ список ниш — просто сети,
    # которыми вылавливаем свежие популярные видео. "" = поиск без запроса.
    "seed_queries": [
        "", "how to", "ai", "story", "explained", "challenge", "tutorial",
        "what if", "i tried", "history", "facts", "build", "money",
        "как", "история", "почему", "что если", "обзор", "я попробовал",
    ],

    # Только длинные видео: минимальная длительность в секундах (900 = 15 минут).
    # Shorts и короткие ролики отбрасываются.
    "min_duration_sec": 900,
    # Какие длительности просить у поиска YouTube: "medium" = 4–20 мин, "long" = больше 20 мин
    "search_durations": ["long", "medium"],

    # Лимит поисковых запросов (каждый стоит 100 ед. квоты из 10 000 в день)
    "max_search_calls": 85,

    # Фильтр «аномалий»
    "max_subscribers": 20_000,   # канал считается маленьким, если подписчиков не больше
    "min_views": 15_000,         # минимум просмотров у видео
    "min_ratio": 3.0,            # просмотры / подписчики не меньше этого
    "new_channel_days": 180,     # «молодой» канал — создан не раньше N дней назад

    # Тема становится нишей, если на неё выстрелило столько РАЗНЫХ каналов
    "min_channels_per_niche": 3,

    # Сколько ниш показывать в отчёте
    "top_niches": 40,

    # Подтягивать подсказки поиска YouTube для топ-ниш (неофициальный эндпоинт)
    "fetch_suggestions": True,
    "suggestions_for_top": 10,

    "output_dir": "radar_output",
}

# Слова, которые не несут смысла темы
STOPWORDS = set("""
a an the and or but if of to in on at by for with from as is are was were be been being it its this that these those
i me my we our you your he she they them his her their what which who whom how why when where than then so too very
can will just not no yes do does did done have has had get got make made new best top full part episode ep vs video
videos shorts short official live day days week year years time first last one two three ever every all more most
about into out up down off over under again only own same some such here there now also back like even still way
youtube channel subscribe watch viral trending fyp foryou funny try tried trying using use got gets going goes
и в во не что он на я с со как а то все она так его но да ты к у же вы за бы по только ее мне было вот от меня
еще нет о из ему теперь когда даже ну вдруг ли если уже или ни быть был него до вас нибудь опять уж вам ведь там
потом себя ничего ей может они тут где есть надо ней для мы тебя их чем была сам чтоб без будто чего раз тоже себе
под будет ж тогда кто этот того потому этого какой совсем ним здесь этом один почти мой тем чтобы нее сейчас были куда
зачем всех никогда можно при наконец два об другой хоть после над больше тот через эти нас про всего них какая много
разве три эту моя впрочем хорошо свою этой перед иногда лучше чуть том нельзя такой им более всегда конечно всю между
это видео шортс шорты выпуск серия часть канал подпишись новый новое новая лучшие топ день дня года год лет
could would should don't doesn't didn't can't won't isn't it's i'm you're that's what's happened happens know knew
people world built thing things someone something everyone really actually never always need want wants let see
look looks find found show shows made makes take takes come comes give gives went go get gets say said tell told
youtubeshorts shortsfeed shortsvideo shortvideo viralvideo viralshorts trend trends trendingshorts reels reel pov
memes meme fun comedy foryoupage explore explorepage tiktok instagram status edit edits capcut whatsapp
лайк подписка рекомендации рек тренд тренды шортсы прикол приколы юмор смешно смешное мем мемы
""".split())

API_BASE = "https://www.googleapis.com/youtube/v3/"


# ════════════════════════════════════════════════════════════════════
# YouTube API
# ════════════════════════════════════════════════════════════════════
class QuotaExceeded(Exception):
    pass


class YouTube:
    def __init__(self, key):
        self.key = key
        self.quota_used = 0

    def call(self, endpoint, params, cost):
        params = dict(params, key=self.key)
        url = API_BASE + endpoint + "?" + urllib.parse.urlencode(params)
        try:
            with urllib.request.urlopen(url, timeout=30) as r:
                self.quota_used += cost
                return json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            body = e.read().decode("utf-8", "ignore")
            if "quotaExceeded" in body or "dailyLimitExceeded" in body:
                raise QuotaExceeded("Дневная квота API исчерпана")
            if e.code in (400, 404):  # например, категория недоступна в регионе
                return None
            if e.code == 403 and ("keyInvalid" in body or "API key not valid" in body):
                sys.exit("Ошибка: неверный API-ключ.")
            if e.code == 403 and "accessNotConfigured" in body:
                sys.exit("Ошибка: в Google Cloud не включён YouTube Data API v3 для этого ключа.")
            print(f"  ! HTTP {e.code} на {endpoint}: {body[:200]}")
            return None
        except urllib.error.URLError as e:
            print(f"  ! Сетевая ошибка: {e}")
            return None

    def trending(self, region, category):
        p = {"part": "id", "chart": "mostPopular", "regionCode": region, "maxResults": 50}
        if category != "0":
            p["videoCategoryId"] = category
        data = self.call("videos", p, 1)
        return [it["id"] for it in (data or {}).get("items", [])]

    def search(self, query, region, published_after, duration=None):
        p = {"part": "id", "type": "video", "order": "viewCount", "maxResults": 50,
             "regionCode": region, "publishedAfter": published_after}
        if duration:
            p["videoDuration"] = duration
        if query:
            p["q"] = query
        data = self.call("search", p, 100)
        return [it["id"]["videoId"] for it in (data or {}).get("items", []) if it.get("id", {}).get("videoId")]

    def videos(self, ids):
        out = []
        ids = list(ids)
        for i in range(0, len(ids), 50):
            data = self.call("videos", {"part": "snippet,statistics,contentDetails",
                                        "id": ",".join(ids[i:i + 50]), "maxResults": 50}, 1)
            out += (data or {}).get("items", [])
        return out

    def channels(self, ids):
        out = []
        ids = list(ids)
        for i in range(0, len(ids), 50):
            data = self.call("channels", {"part": "snippet,statistics",
                                          "id": ",".join(ids[i:i + 50]), "maxResults": 50}, 1)
            out += (data or {}).get("items", [])
        return out


def fetch_suggestions(term, lang="en"):
    """Подсказки автодополнения YouTube (неофициальный эндпоинт, без квоты)."""
    url = ("https://suggestqueries.google.com/complete/search?client=firefox&ds=yt&hl="
           + lang + "&q=" + urllib.parse.quote(term))
    try:
        with urllib.request.urlopen(url, timeout=10) as r:
            data = json.loads(r.read().decode("utf-8", "ignore"))
            return [s for s in data[1] if s.lower() != term.lower()][:8]
    except Exception:
        return []


# ════════════════════════════════════════════════════════════════════
# Утилиты
# ════════════════════════════════════════════════════════════════════
def parse_time(s):
    return dt.datetime.fromisoformat(s.replace("Z", "+00:00"))


def duration_seconds(d):
    m = re.match(r"P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?", d or "")
    if not m:
        return 0
    dd, hh, mm, ss = (int(x) if x else 0 for x in m.groups())
    return dd * 86400 + hh * 3600 + mm * 60 + ss


TOKEN_RE = re.compile(r"[^\W\d_][\w'’-]*", re.UNICODE)


def tokens(text):
    return [t.strip("'’-") for t in TOKEN_RE.findall((text or "").lower())]


def extract_terms(title, tags):
    """Возвращает набор тем-кандидатов: слова, пары слов, короткие теги."""
    toks = [t for t in tokens(title) if t]
    terms = set()
    for t in toks:
        if len(t) >= 3 and t not in STOPWORDS:
            terms.add(t)
    for a, b in zip(toks, toks[1:]):
        if a not in STOPWORDS and b not in STOPWORDS and len(a) >= 2 and len(b) >= 2:
            terms.add(a + " " + b)
    for tag in (tags or [])[:25]:
        tt = [t for t in tokens(tag) if t]
        if 1 <= len(tt) <= 3 and not all(t in STOPWORDS for t in tt):
            if len(tt) == 1 and (len(tt[0]) < 3 or tt[0] in STOPWORDS):
                continue
            terms.add(" ".join(tt))
    return terms


def median(xs):
    return statistics.median(xs) if xs else 0


def fmt_num(n):
    n = float(n)
    for unit, div in (("M", 1e6), ("K", 1e3)):
        if abs(n) >= div:
            return f"{n / div:.1f}{unit}"
    return f"{n:.0f}"


# ════════════════════════════════════════════════════════════════════
# Сбор данных
# ════════════════════════════════════════════════════════════════════
def collect(yt, cfg):
    now = dt.datetime.now(dt.timezone.utc)
    after = (now - dt.timedelta(days=cfg["days_back"])).strftime("%Y-%m-%dT%H:%M:%SZ")
    ids = set()

    print("[1/4] Тренды по категориям…")
    for region in cfg["regions"]:
        for cat in cfg["trend_categories"]:
            ids.update(yt.trending(region, cat))
    print(f"      видео: {len(ids)}")

    print("[2/4] Широкий поиск свежих популярных видео…")
    calls = 0
    try:
        for q in cfg["seed_queries"]:
            for region in cfg["regions"]:
                for dur in cfg.get("search_durations") or [None]:
                    if calls >= cfg["max_search_calls"]:
                        break
                    ids.update(yt.search(q, region, after, dur))
                    calls += 1
    except QuotaExceeded as e:
        print("  !", e, "— продолжаю с тем, что собрано")
    print(f"      видео: {len(ids)} (поисковых запросов: {calls})")

    print("[3/4] Статистика видео и каналов…")
    raw_videos = yt.videos(ids)
    ch_ids = {v["snippet"]["channelId"] for v in raw_videos}
    raw_channels = yt.channels(ch_ids)

    channels = {}
    for c in raw_channels:
        st = c.get("statistics", {})
        channels[c["id"]] = {
            "id": c["id"],
            "title": c["snippet"].get("title", ""),
            "subs": None if st.get("hiddenSubscriberCount") else int(st.get("subscriberCount", 0)),
            "video_count": int(st.get("videoCount", 0)),
            "created": c["snippet"].get("publishedAt"),
        }

    videos = []
    for v in raw_videos:
        sn, st = v["snippet"], v.get("statistics", {})
        videos.append({
            "id": v["id"],
            "title": sn.get("title", ""),
            "tags": sn.get("tags", []),
            "channel_id": sn["channelId"],
            "published": sn["publishedAt"],
            "views": int(st.get("viewCount", 0)),
            "likes": int(st.get("likeCount", 0)),
            "comments": int(st.get("commentCount", 0)),
            "duration": duration_seconds(v.get("contentDetails", {}).get("duration")),
            "lang": sn.get("defaultAudioLanguage") or sn.get("defaultLanguage") or "",
        })
    return videos, channels


# ════════════════════════════════════════════════════════════════════
# Анализ
# ════════════════════════════════════════════════════════════════════
def analyze(videos, channels, cfg, now=None):
    now = now or dt.datetime.now(dt.timezone.utc)
    seed_terms = set()
    for q in cfg.get("seed_queries", []):
        tt = tokens(q)
        if tt:
            seed_terms.add(" ".join(tt))
            seed_terms.update(tt)
    max_age = dt.timedelta(days=cfg["days_back"])

    enriched = []
    for v in videos:
        ch = channels.get(v["channel_id"])
        if not ch or ch["subs"] is None:
            continue
        pub = parse_time(v["published"])
        if now - pub > max_age:
            continue
        if v.get("duration", 0) < cfg.get("min_duration_sec", 0):
            continue  # короткие ролики и Shorts не учитываем
        age_h = max((now - pub).total_seconds() / 3600, 1)
        ch_age_days = (now - parse_time(ch["created"])).days if ch.get("created") else 9999
        v = dict(v)
        v.update({
            "subs": ch["subs"],
            "channel_title": ch["title"],
            "channel_age_days": ch_age_days,
            "ratio": v["views"] / max(ch["subs"], 100),
            "vph": v["views"] / age_h,
            "is_new_channel": ch_age_days <= cfg["new_channel_days"],
            "is_short": 0 < v["duration"] <= 180,
            "terms": extract_terms(v["title"], v["tags"]),
        })
        enriched.append(v)

    outliers = [v for v in enriched
                if v["subs"] <= cfg["max_subscribers"]
                and v["views"] >= cfg["min_views"]
                and v["ratio"] >= cfg["min_ratio"]]

    # тема → все видео с ней (для оценки насыщенности)
    all_by_term = defaultdict(int)
    for v in enriched:
        for t in v["terms"]:
            all_by_term[t] += 1

    out_by_term = defaultdict(list)
    for v in outliers:
        for t in v["terms"]:
            out_by_term[t].append(v)

    candidates = []
    for term, vs in out_by_term.items():
        if term in seed_terms:
            continue  # слово из поисковой «затравки» — не ниша, а артефакт сбора
        chans = {v["channel_id"] for v in vs}
        if len(chans) < cfg["min_channels_per_niche"]:
            continue
        # одно видео на канал — лучшее
        best = {}
        for v in vs:
            if v["channel_id"] not in best or v["ratio"] > best[v["channel_id"]]["ratio"]:
                best[v["channel_id"]] = v
        vs1 = list(best.values())
        n_ch = len(vs1)
        med_ratio = median([v["ratio"] for v in vs1])
        new_share = sum(v["is_new_channel"] for v in vs1) / n_ch
        outlier_share = len(vs) / max(all_by_term[term], 1)
        specificity = 1.25 if " " in term else 1.0
        score = n_ch * math.log10(1 + med_ratio) * (1 + new_share) * (0.5 + outlier_share) * specificity
        candidates.append({
            "term": term,
            "score": score,
            "channels": n_ch,
            "videos": vs1,
            "video_ids": {v["id"] for v in vs},
            "median_views": median([v["views"] for v in vs1]),
            "median_subs": median([v["subs"] for v in vs1]),
            "median_ratio": med_ratio,
            "median_vph": median([v["vph"] for v in vs1]),
            "new_share": new_share,
            "short_share": sum(v["is_short"] for v in vs1) / n_ch,
            "median_minutes": median([v["duration"] for v in vs1]) / 60,
            "outlier_share": outlier_share,
            "total_videos_with_term": all_by_term[term],
            "aliases": [],
        })

    # схлопываем похожие темы (одни и те же видео) в одну нишу
    candidates.sort(key=lambda c: (-round(c["score"], 6), -len(c["term"]), c["term"]))
    niches = []
    for c in candidates:
        merged = False
        for n in niches:
            overlap = len(c["video_ids"] & n["video_ids"]) / len(c["video_ids"])
            if overlap >= 0.6:
                if len(n["aliases"]) < 6:
                    n["aliases"].append(c["term"])
                merged = True
                break
        if not merged:
            niches.append(c)

    return niches[:cfg["top_niches"]], outliers, enriched


def apply_history(niches, history_path):
    history = {}
    if os.path.exists(history_path):
        with open(history_path, encoding="utf-8") as f:
            history = json.load(f)
    past_runs = sorted(history.keys())
    last = history[past_runs[-1]] if past_runs else {}
    seen_before = set()
    for k in past_runs:
        seen_before.update(history[k].keys())

    for n in niches:
        if not past_runs:
            n["trend"] = "—"
        elif n["term"] not in seen_before:
            n["trend"] = "НОВАЯ"
        elif n["term"] in last:
            d = n["channels"] - last[n["term"]]
            n["trend"] = f"{'+' if d >= 0 else ''}{d} кан."
        else:
            n["trend"] = "вернулась"

    stamp = dt.datetime.now().strftime("%Y-%m-%d %H:%M")
    history[stamp] = {n["term"]: n["channels"] for n in niches}
    # храним последние 60 запусков
    for k in sorted(history.keys())[:-60]:
        del history[k]
    with open(history_path, "w", encoding="utf-8") as f:
        json.dump(history, f, ensure_ascii=False, indent=1)
    return len(past_runs)


# ════════════════════════════════════════════════════════════════════
# Отчёты
# ════════════════════════════════════════════════════════════════════
def write_csv(niches, outliers, out_dir):
    with open(os.path.join(out_dir, "niches.csv"), "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Ниша", "Похожие темы", "Оценка", "Каналов", "Медиана просмотров",
                    "Медиана подписчиков", "Просмотры/подписчики", "Просмотров в час",
                    "Доля молодых каналов", "Медиана длительности, мин", "Тренд", "Примеры"])
        for n in niches:
            w.writerow([n["term"], ", ".join(n["aliases"]), round(n["score"], 2), n["channels"],
                        int(n["median_views"]), int(n["median_subs"]), round(n["median_ratio"], 1),
                        int(n["median_vph"]), f"{n['new_share']:.0%}", round(n["median_minutes"]),
                        n.get("trend", ""),
                        " | ".join("https://youtu.be/" + v["id"] for v in
                                   sorted(n["videos"], key=lambda v: -v["ratio"])[:5])])
    with open(os.path.join(out_dir, "outlier_videos.csv"), "w", newline="", encoding="utf-8-sig") as f:
        w = csv.writer(f, delimiter=";")
        w.writerow(["Видео", "Ссылка", "Канал", "Подписчики", "Просмотры", "Просмотры/подписчики",
                    "Просмотров в час", "Возраст канала (дн.)", "Длительность (сек)", "Опубликовано"])
        for v in sorted(outliers, key=lambda v: -v["ratio"]):
            w.writerow([v["title"], "https://youtu.be/" + v["id"], v["channel_title"], v["subs"],
                        v["views"], round(v["ratio"], 1), int(v["vph"]), v["channel_age_days"],
                        v["duration"], v["published"][:10]])


def write_md(niches, outliers, enriched, cfg, out_dir, quota):
    """Короткая сводка в Markdown — красиво открывается прямо на GitHub."""
    now = dt.datetime.now().strftime("%d.%m.%Y %H:%M")
    esc = lambda t: str(t).replace("|", "/").replace("\n", " ")
    lines = [f"# Радар ниш YouTube — {now}", "",
             f"Регионы: {', '.join(cfg['regions'])} · видео за {cfg['days_back']} дн. · "
             f"только видео от {cfg.get('min_duration_sec', 0) // 60} мин · проанализировано {len(enriched)} видео · аномалий {len(outliers)} · квота {quota}", "",
             "| # | Ниша | Тренд | Каналов | Медиана просм. | Медиана подп. | Просм./подп. | Молодых | Пример |",
             "|---|---|---|---|---|---|---|---|---|"]
    for i, n in enumerate(niches[:30], 1):
        best = max(n["videos"], key=lambda v: v["ratio"])
        alias = f" <br><sub>{esc(', '.join(n['aliases'][:3]))}</sub>" if n["aliases"] else ""
        lines.append(f"| {i} | **{esc(n['term'])}**{alias} | {esc(n.get('trend', '—'))} | {n['channels']} | "
                     f"{fmt_num(n['median_views'])} | {fmt_num(n['median_subs'])} | ×{n['median_ratio']:.1f} | "
                     f"{n['new_share']:.0%} | [{esc(best['title'][:50])}](https://youtu.be/{best['id']}) |")
    if not niches:
        lines.append("| — | Ниш не найдено — ослабьте фильтры в CONFIG | | | | | | | |")
    lines += ["", "Нажмите на нишу в таблице выше или прокрутите вниз — там каналы и видео по каждой нише.", ""]

    # Подробно: каналы и видео по каждой нише
    lines += ["## Каналы и видео по нишам", ""]
    for i, n in enumerate(niches[:30], 1):
        lines.append(f"### {i}. {esc(n['term'])}")
        if n["aliases"]:
            lines.append(f"Похожие темы: {esc(', '.join(n['aliases']))}  ")
        lines.append(f"Каналов: {n['channels']} · медиана ×{n['median_ratio']:.1f} просмотров к подписчикам · "
                     f"молодых каналов {n['new_share']:.0%}")
        lines.append("")
        for v in sorted(n["videos"], key=lambda v: -v["ratio"])[:8]:
            age = f" · канал создан {v['channel_age_days']} дн. назад" if v["is_new_channel"] else ""
            fmt = f" · {v['duration'] // 60} мин"
            lines.append(f"- [{esc(v['title'][:80])}](https://youtu.be/{v['id']}) — "
                         f"канал [{esc(v['channel_title'][:40])}](https://www.youtube.com/channel/{v['channel_id']}) · "
                         f"{fmt_num(v['views'])} просм. / {fmt_num(v['subs'])} подп. (×{v['ratio']:.0f}){age}{fmt}")
        lines.append("")

    # Все аномалии
    lines += ["## Топ-50 видео-аномалий", "",
              "| Видео | Канал | Подп. | Просм. | ×Рост | Канал, дн. |", "|---|---|---|---|---|---|"]
    for v in sorted(outliers, key=lambda v: -v["ratio"])[:50]:
        lines.append(f"| [{esc(v['title'][:60])}](https://youtu.be/{v['id']}) | "
                     f"[{esc(v['channel_title'][:30])}](https://www.youtube.com/channel/{v['channel_id']}) | "
                     f"{fmt_num(v['subs'])} | {fmt_num(v['views'])} | ×{v['ratio']:.0f} | {v['channel_age_days']} |")
    lines += ["", "Таблицы для Excel: `niches.csv`, `outlier_videos.csv`."]
    with open(os.path.join(out_dir, "NICHES.md"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")


def write_html(niches, outliers, enriched, cfg, out_dir, quota, runs_before, demo):
    e = html.escape
    now = dt.datetime.now().strftime("%d.%m.%Y %H:%M")

    rows = []
    for i, n in enumerate(niches, 1):
        ex = sorted(n["videos"], key=lambda v: -v["ratio"])[:4]
        examples = "".join(
            f'<li><a href="https://youtu.be/{e(v["id"])}" target="_blank" rel="noopener">{e(v["title"][:90])}</a>'
            f'<span class="muted"> · <a href="https://www.youtube.com/channel/{e(v["channel_id"])}" target="_blank" rel="noopener">{e(v["channel_title"][:30])}</a> · {fmt_num(v["views"])} просм. / {fmt_num(v["subs"])} подп.'
            f' · {v["duration"] // 60} мин'
            f'{" · канал " + str(v["channel_age_days"]) + " дн." if v["is_new_channel"] else ""}</span></li>'
            for v in ex)
        aliases = (f'<div class="aliases">также: {e(", ".join(n["aliases"]))}</div>' if n["aliases"] else "")
        sugg = (f'<div class="sugg">подсказки поиска: {e(", ".join(n["suggestions"]))}</div>'
                if n.get("suggestions") else "")
        trend = n.get("trend", "—")
        tcls = "new" if trend == "НОВАЯ" else ("up" if trend.startswith("+") and trend != "+0 кан." else "")
        rows.append(f"""
<tr>
  <td class="num">{i}</td>
  <td><div class="term">{e(n["term"])}</div>{aliases}
      <details><summary>{n["channels"]} каналов · примеры</summary><ul>{examples}</ul>{sugg}</details></td>
  <td class="num"><b>{n["score"]:.1f}</b></td>
  <td class="num">{n["channels"]}</td>
  <td class="num">{fmt_num(n["median_views"])}</td>
  <td class="num">{fmt_num(n["median_subs"])}</td>
  <td class="num">×{n["median_ratio"]:.1f}</td>
  <td class="num">{fmt_num(n["median_vph"])}</td>
  <td class="num">{n["new_share"]:.0%}</td>
  <td class="num">{n["median_minutes"]:.0f}</td>
  <td class="num"><span class="tag {tcls}">{e(trend)}</span></td>
</tr>""")

    vrows = "".join(f"""
<tr><td><a href="https://youtu.be/{e(v["id"])}" target="_blank" rel="noopener">{e(v["title"][:100])}</a></td>
<td>{e(v["channel_title"][:35])}</td><td class="num">{fmt_num(v["subs"])}</td>
<td class="num">{fmt_num(v["views"])}</td><td class="num">×{v["ratio"]:.1f}</td>
<td class="num">{fmt_num(v["vph"])}</td><td class="num">{v["channel_age_days"]}</td></tr>"""
                    for v in sorted(outliers, key=lambda v: -v["ratio"])[:100])

    demo_banner = ('<div class="banner">Демо-режим: данные сгенерированы для проверки, это не реальные видео.</div>'
                   if demo else "")
    hist_note = ("Первый запуск — колонка «Тренд» заполнится со следующего запуска."
                 if runs_before == 0 else f"Сравнение с {runs_before} прошлыми запусками.")

    page = f"""<!doctype html>
<html lang="ru"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Радар ниш YouTube</title>
<style>
:root{{--bg:#f7f6f3;--card:#fff;--fg:#1d1d1f;--muted:#6b6b70;--line:#e4e2dc;--acc:#d6332a;--up:#1f8a4c}}
@media (prefers-color-scheme:dark){{:root{{--bg:#141416;--card:#1d1d21;--fg:#ececef;--muted:#9a9aa2;--line:#2e2e34;--acc:#ff5a4f;--up:#4cc27f}}}}
*{{box-sizing:border-box}}body{{margin:0;background:var(--bg);color:var(--fg);font:14px/1.45 system-ui,-apple-system,Segoe UI,Roboto,sans-serif}}
.wrap{{max-width:1300px;margin:0 auto;padding:24px 16px 60px}}
h1{{font-size:26px;margin:0 0 4px}}h2{{font-size:18px;margin:36px 0 10px}}
.muted{{color:var(--muted)}}a{{color:inherit}}
.stats{{display:flex;flex-wrap:wrap;gap:10px;margin:18px 0}}
.stat{{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:10px 14px}}
.stat b{{display:block;font-size:20px}}
.banner{{background:var(--acc);color:#fff;padding:8px 12px;border-radius:8px;margin:12px 0}}
.tbl{{overflow-x:auto;background:var(--card);border:1px solid var(--line);border-radius:12px}}
table{{border-collapse:collapse;width:100%;min-width:900px}}
th,td{{padding:9px 10px;border-bottom:1px solid var(--line);vertical-align:top;text-align:left}}
th{{font-size:12px;color:var(--muted);font-weight:600;position:sticky;top:0;background:var(--card)}}
td.num,th.num{{text-align:right;white-space:nowrap}}
.term{{font-weight:650;font-size:15px}}.aliases,.sugg{{font-size:12px;color:var(--muted)}}
details summary{{cursor:pointer;font-size:12px;color:var(--muted);margin-top:4px}}
details ul{{margin:6px 0;padding-left:18px}}details li{{margin:3px 0}}
.tag{{font-size:12px;padding:2px 7px;border-radius:20px;border:1px solid var(--line)}}
.tag.new{{background:var(--acc);color:#fff;border-color:var(--acc)}}.tag.up{{color:var(--up);border-color:var(--up)}}
.legend{{font-size:13px;color:var(--muted);max-width:900px}}
</style></head><body><div class="wrap">
<h1>Радар ниш YouTube</h1>
<div class="muted">{now} · регионы: {e(", ".join(cfg["regions"]))} · видео за {cfg["days_back"]} дн. · только ролики от {cfg.get("min_duration_sec", 0) // 60} мин · {e(hist_note)}</div>
{demo_banner}
<div class="stats">
 <div class="stat"><b>{len(enriched)}</b>свежих видео проанализировано</div>
 <div class="stat"><b>{len(outliers)}</b>аномалий (маленький канал, много просмотров)</div>
 <div class="stat"><b>{len(niches)}</b>ниш-кандидатов</div>
 <div class="stat"><b>{quota}</b>ед. квоты API потрачено</div>
</div>
<h2>Ниши-кандидаты</h2>
<div class="tbl"><table>
<tr><th class="num">#</th><th>Ниша</th><th class="num">Оценка</th><th class="num">Каналов</th>
<th class="num">Медиана просм.</th><th class="num">Медиана подп.</th><th class="num">Просм./подп.</th>
<th class="num">Просм./час</th><th class="num">Молодых каналов</th><th class="num">Длит., мин</th><th class="num">Тренд</th></tr>
{"".join(rows) or '<tr><td colspan="11">Ниш не найдено — ослабьте фильтры в CONFIG.</td></tr>'}
</table></div>
<p class="legend"><b>Как читать.</b> «Каналов» — сколько разных маленьких каналов (до {fmt_num(cfg["max_subscribers"])} подп.)
одновременно выстрелили на этой теме. «Просм./подп.» — во сколько раз просмотры видео превышают подписчиков канала.
«Молодых каналов» — доля каналов младше {cfg["new_channel_days"]} дней: высокая доля значит, что люди только что зашли в нишу.
«Тренд»: НОВАЯ — тема не встречалась в прошлых запусках. Лучшие кандидаты: много каналов, высокое соотношение, много молодых каналов.
Всегда открывайте примеры и проверяйте глазами — часть тем окажется разовым хайпом или шумом.</p>
<h2>Видео-аномалии (топ-100)</h2>
<div class="tbl"><table>
<tr><th>Видео</th><th>Канал</th><th class="num">Подп.</th><th class="num">Просм.</th>
<th class="num">Просм./подп.</th><th class="num">Просм./час</th><th class="num">Возраст канала, дн.</th></tr>
{vrows}
</table></div>
</div></body></html>"""
    path = os.path.join(out_dir, "report.html")
    with open(path, "w", encoding="utf-8") as f:
        f.write(page)
    return path


# ════════════════════════════════════════════════════════════════════
# Демо-данные (проверка без API-ключа)
# ════════════════════════════════════════════════════════════════════
def demo_data(cfg):
    rnd = random.Random(42)
    now = dt.datetime.now(dt.timezone.utc)
    iso = lambda d: d.strftime("%Y-%m-%dT%H:%M:%SZ")
    channels, videos = {}, []

    def add_channel(subs, age_days):
        cid = "UC" + "".join(rnd.choice("abcdefghijklmnopqrstuvwxyz0123456789") for _ in range(10))
        channels[cid] = {"id": cid, "title": "Channel " + cid[2:7], "subs": subs, "video_count": rnd.randint(3, 400),
                         "created": iso(now - dt.timedelta(days=age_days))}
        return cid

    generic = ["my morning routine", "funny moments compilation", "reacting to comments", "car review 2026",
               "best gaming moments", "travel vlog japan", "cooking pasta at home", "football highlights",
               "unboxing new phone", "workout at home", "как я провёл выходные", "обзор нового телефона",
               "смешные моменты", "рецепт борща"]
    for _ in range(600):  # шум: просмотры пропорциональны подписчикам
        subs = int(10 ** rnd.uniform(2.5, 6.5))
        cid = add_channel(subs, rnd.randint(100, 4000))
        videos.append({"id": "v" + str(len(videos)), "title": rnd.choice(generic).title(), "tags": [],
                       "channel_id": cid, "published": iso(now - dt.timedelta(hours=rnd.randint(5, 160))),
                       "views": int(subs * rnd.uniform(0.05, 1.5)), "likes": 0, "comments": 0,
                       "duration": rnd.randint(30, 1500), "lang": "en"})

    emerging = {
        "ai cooking": ["AI cooking robot makes {x}", "I let AI cooking assistant plan my {x}", "AI cooking: {x} in 5 min"],
        "faceless history": ["faceless history: the fall of {x}", "Dark faceless history of {x}"],
        "retro laptop restoration": ["Retro laptop restoration — {x} from 1998", "$5 retro laptop restoration {x}"],
        "сонные истории": ["Сонные истории: {x}", "Сонные истории для взрослых про {x}"],
        "lego technic": ["Lego Technic {x} that actually works", "I built a working {x} with Lego Technic"],
    }
    fill = ["pizza", "rome", "thinkpad", "sushi", "bridge", "engine", "titanic", "samurai", "крепость", "маяк"]
    for niche, templates in emerging.items():
        for _ in range(rnd.randint(4, 9)):
            subs = rnd.randint(300, 15000)
            cid = add_channel(subs, rnd.randint(10, 400))
            videos.append({"id": "v" + str(len(videos)), "title": rnd.choice(templates).format(x=rnd.choice(fill)),
                           "tags": [niche], "channel_id": cid,
                           "published": iso(now - dt.timedelta(hours=rnd.randint(5, 150))),
                           "views": int(subs * rnd.uniform(4, 60)) + 30000, "likes": 0, "comments": 0,
                           "duration": rnd.choice([960, 1300, 1800, 2700]), "lang": "en"})
    return videos, channels


# ════════════════════════════════════════════════════════════════════
def main():
    ap = argparse.ArgumentParser(description="Радар зарождающихся ниш YouTube")
    ap.add_argument("--key", help="YouTube Data API v3 ключ (или переменная окружения YT_API_KEY)")
    ap.add_argument("--demo", action="store_true", help="запуск на тестовых данных без API")
    ap.add_argument("--regions", help="страны через запятую, например US,RU,PL")
    ap.add_argument("--days", type=int, help="сколько дней назад смотреть")
    ap.add_argument("--max-subs", type=int, help="максимум подписчиков у «маленького» канала")
    ap.add_argument("--out", help="папка для результатов")
    ap.add_argument("--history-url", help="URL прошлого history.json (для запусков в GitLab CI)")
    args = ap.parse_args()

    cfg = dict(CONFIG)
    if args.regions:
        cfg["regions"] = [r.strip().upper() for r in args.regions.split(",") if r.strip()]
    if args.days:
        cfg["days_back"] = args.days
    if args.max_subs:
        cfg["max_subscribers"] = args.max_subs

    out_dir = args.out or (cfg["output_dir"] + ("_demo" if args.demo else ""))
    os.makedirs(out_dir, exist_ok=True)

    hist_path = os.path.join(out_dir, "history.json")
    if args.history_url and not os.path.exists(hist_path):
        try:
            req = urllib.request.Request(args.history_url)
            if os.environ.get("CI_JOB_TOKEN"):
                req.add_header("JOB-TOKEN", os.environ["CI_JOB_TOKEN"])
            with urllib.request.urlopen(req, timeout=20) as r:
                data = r.read()
            json.loads(data.decode("utf-8"))
            with open(hist_path, "wb") as f:
                f.write(data)
            print("История прошлых запусков загружена.")
        except Exception as ex:
            print(f"История не найдена ({ex}) — считаю это первым запуском.")

    quota = 0
    if args.demo:
        print("Демо-режим: генерирую тестовые данные…")
        videos, channels = demo_data(cfg)
    else:
        key = args.key or os.environ.get("YT_API_KEY")
        if not key:
            sys.exit("Нужен API-ключ: python niche_radar.py --key ВАШ_КЛЮЧ  (или --demo для проверки)")
        yt = YouTube(key)
        videos, channels = collect(yt, cfg)
        quota = yt.quota_used
        with open(os.path.join(out_dir, "raw_last_run.json"), "w", encoding="utf-8") as f:
            json.dump({"videos": videos, "channels": channels}, f, ensure_ascii=False)

    print("[4/4] Ищу аномалии и выделяю ниши…")
    niches, outliers, enriched = analyze(videos, channels, cfg)
    runs_before = apply_history(niches, os.path.join(out_dir, "history.json"))

    if cfg["fetch_suggestions"] and not args.demo:
        for n in niches[:cfg["suggestions_for_top"]]:
            lang = "ru" if re.search("[а-яё]", n["term"]) else "en"
            n["suggestions"] = fetch_suggestions(n["term"], lang)

    write_csv(niches, outliers, out_dir)
    report = write_html(niches, outliers, enriched, cfg, out_dir, quota, runs_before, args.demo)
    write_md(niches, outliers, enriched, cfg, out_dir, quota)

    print(f"\nГотово. Видео: {len(enriched)}, аномалий: {len(outliers)}, ниш: {len(niches)}, квота: {quota}")
    for i, n in enumerate(niches[:10], 1):
        print(f"  {i:2}. {n['term']:<30} каналов: {n['channels']:<3} ×{n['median_ratio']:.1f}  "
              f"молодых: {n['new_share']:.0%}  {n.get('trend', '')}")
    print(f"\nОтчёт: {os.path.abspath(report)}")


if __name__ == "__main__":
    main()
