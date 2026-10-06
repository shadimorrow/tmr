import React, { useEffect, useMemo, useRef, useState } from 'react';
import { createRoot } from 'react-dom/client';
import L from 'leaflet';
import 'leaflet/dist/leaflet.css';
import './styles.css';

const DATA_URL = 'https://raw.githubusercontent.com/mostafa-kheibary/tehran-metro-data/main/data/stations.json';
const OSM_URL = 'https://tile.openstreetmap.org/{z}/{x}/{y}.png';
const OSM_ATTR = '&copy; <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noreferrer">OpenStreetMap</a> contributors';
const LINE_COLORS = { 1:'#e52b3a', 2:'#2e5d9f', 3:'#399447', 4:'#efc31d', 5:'#19a566', 6:'#7441a8', 7:'#8c267d', 8:'#f47b25', 9:'#00a5a8', 10:'#6b7280' };

const MQ_STACK = window.matchMedia('(min-width:1024px)');
const MQ_LAND = window.matchMedia('(orientation:landscape) and (max-height:620px) and (min-width:640px)');
const isStacked = () => !MQ_STACK.matches && !MQ_LAND.matches;
const clamp01 = v => v < 0 ? 0 : v > 1 ? 1 : v;
const FOLD_CHIP_H = 44;

function haversine(a,b){
  const R=6371000, p=Math.PI/180, dLat=(b.lat-a.lat)*p, dLon=(b.lng-a.lng)*p;
  const x=Math.sin(dLat/2)**2+Math.cos(a.lat*p)*Math.cos(b.lat*p)*Math.sin(dLon/2)**2;
  return 2*R*Math.asin(Math.sqrt(x));
}
function fmtDistance(m){ return m < 1000 ? `${Math.round(m)} متر` : `${(m/1000).toFixed(1)} کیلومتر`; }
function normalize(s){ return String(s||'').toLowerCase().replace(/[يى]/g,'ی').replace(/ك/g,'ک').replace(/[‌ـ]/g,'').trim(); }
function routeGradient(route){
  const colors=[...new Set((route?.steps||[]).map(s=>LINE_COLORS[s.line]||'#555'))];
  return colors.length?`linear-gradient(90deg,${colors.join(',')})`:'none';
}

function buildModel(raw){
  const stations = Object.entries(raw)
    .filter(([,s]) => s && !s.disabled && Number.isFinite(+s.latitude) && Number.isFinite(+s.longitude))
    .map(([id,s]) => ({
      id, name:s.name||id, fa:s.translations?.fa||s.name||id,
      lat:+s.latitude, lng:+s.longitude, lines:(s.lines||[]).map(Number), relations:s.relations||[]
    }));
  const byId = new Map(stations.map(s=>[s.id,s]));
  const graph = new Map(stations.map(s=>[s.id,[]]));
  for(const s of stations){
    for(const rid of s.relations){
      const n=byId.get(rid); if(!n) continue;
      const common=s.lines.filter(x=>n.lines.includes(x));
      graph.get(s.id).push({to:n.id,lines:common.length?common:s.lines});
    }
  }
  return {stations,byId,graph};
}

class MinHeap{
  constructor(){this.a=[]}
  push(x){const a=this.a;a.push(x);let i=a.length-1;while(i){let p=(i-1)>>1;if(a[p][0]<=x[0])break;a[i]=a[p];i=p;}a[i]=x}
  pop(){const a=this.a;if(!a.length)return;const top=a[0],x=a.pop();if(a.length){let i=0;while(true){let l=i*2+1;if(l>=a.length)break;let r=l+1,c=r<a.length&&a[r][0]<a[l][0]?r:l;if(a[c][0]>=x[0])break;a[i]=a[c];i=c}a[i]=x}return top}
}

function shortestRoute(model,startId,endId,transferPenalty=5){
  if(startId===endId)return {stations:[startId],steps:[],transfers:0,cost:0};
  const start=model.byId.get(startId), target=model.byId.get(endId); if(!start||!target)return null;
  const dist=new Map(), prev=new Map(), heap=new MinHeap();
  for(const line of start.lines){const k=`${startId}|${line}`;dist.set(k,0);heap.push([0,k,startId,line]);}
  let endKey=null;
  while(heap.a.length){
    const [d,key,u,line]=heap.pop(); if(d!==dist.get(key))continue;
    if(u===endId){endKey=key;break}
    for(const e of model.graph.get(u)||[]){
      for(const nextLine of e.lines){
        const nk=`${e.to}|${nextLine}`;
        const w=1+(nextLine===line?0:transferPenalty);
        const nd=d+w;
        if(nd<(dist.get(nk)??Infinity)){dist.set(nk,nd);prev.set(nk,{key,u,line,nextLine});heap.push([nd,nk,e.to,nextLine]);}
      }
    }
  }
  if(!endKey)return null;
  const states=[]; let k=endKey;
  while(k){states.push(k);const p=prev.get(k);k=p?.key||null}
  states.reverse();
  const steps=[];
  for(let i=1;i<states.length;i++){
    const [a,lineA]=states[i-1].split('|'),[b,lineB]=states[i].split('|');
    steps.push({from:a,to:b,line:+lineB,changed:+lineA!==+lineB});
  }
  return {stations:states.map(s=>s.split('|')[0]).filter((x,i,a)=>i===0||x!==a[i-1]),steps,transfers:steps.filter(x=>x.changed).length,cost:dist.get(endKey)};
}

function App(){
  const [model,setModel]=useState(null);
  const [error,setError]=useState('');
  const [origin,setOrigin]=useState('');
  const [query,setQuery]=useState('');
  const [destination,setDestination]=useState(null);
  const [route,setRoute]=useState(null);
  const [loading,setLoading]=useState(true);
  const [transferPenalty,setTransferPenalty]=useState(5);
  const [showStations,setShowStations]=useState(true);
  const [theme,setTheme]=useState(()=>window.matchMedia?.('(prefers-color-scheme: light)').matches?'light':'dark');
  const mapRef=useRef(null), mapEl=useRef(null), markers=useRef(new Map()), routeLayer=useRef(null), destMarker=useRef(null);
  const workspaceRef=useRef(null), shellRef=useRef(null), panelRef=useRef(null);
  const fold=useRef({p:0,raf:0,full:0,cellW:0,h0:0,m0:0});
  const scheduleFold=useRef(()=>{});

  useEffect(()=>{
    document.documentElement.setAttribute('data-theme',theme);
    document.querySelector('meta[name="theme-color"]')?.setAttribute('content',theme==='light'?'#fbf1c7':'#282828');
  },[theme]);

  useEffect(()=>{
    (async()=>{
      try{
        const r=await fetch(DATA_URL,{cache:'no-store'}); if(!r.ok)throw Error('data');
        setModel(buildModel(await r.json()));
      }catch(e){setError('داده‌ی ایستگاه‌ها بارگذاری نشد. اتصال اینترنت را بررسی کنید.')}
      finally{setLoading(false)}
    })();
  },[]);

  useEffect(()=>{
    if(!mapEl.current||mapRef.current)return;
    const map=L.map(mapEl.current,{zoomControl:false,preferCanvas:true}).setView([35.715,51.42],11.5);
    L.control.zoom({position:'bottomright'}).addTo(map);
    L.tileLayer(OSM_URL,{maxZoom:19,attribution:OSM_ATTR,referrerPolicy:'strict-origin-when-cross-origin'}).addTo(map);
    map.on('click',e=>setDestination({lat:e.latlng.lat,lng:e.latlng.lng}));
    mapRef.current=map;
    const onResize=()=>map.invalidateSize({debounceMoveend:true});
    window.addEventListener('resize',onResize);
    const t=setTimeout(onResize,350);
    return()=>{window.removeEventListener('resize',onResize);clearTimeout(t);map.remove()};
  },[]);

  useEffect(()=>{
    const g=fold.current;
    const ws=workspaceRef.current, shell=shellRef.current, panel=panelRef.current;
    if(!ws||!shell||!panel)return;

    const measure=()=>{
      const row=ws.style.gridTemplateRows, h=shell.style.height;
      ws.style.gridTemplateRows=''; shell.style.height='';
      g.full=shell.offsetHeight; g.cellW=shell.offsetWidth;
      ws.style.gridTemplateRows=row; shell.style.height=h;
      g.h0=panel.clientHeight||g.full;
      g.m0=panel.scrollHeight-g.h0;
    };

    const apply=p=>{
      g.p=p;
      if(!g.full)return;
      if(p<=0){
        ws.style.gridTemplateRows=''; shell.style.height=''; shell.style.transform='';
        shell.style.borderWidth=''; shell.style.borderRadius=''; shell.style.boxShadow='';
        shell.style.setProperty('--p','0'); shell.style.setProperty('--s','1');
        shell.classList.remove('folded','folding');
        mapRef.current?.invalidateSize({debounceMoveend:true});
        return;
      }
      const e=p*p*(3-2*p);
      const s=Math.max(.05,1-(1-Math.min(.5,FOLD_CHIP_H/g.full))*e);
      const ty=5*e;
      shell.style.height=g.full+'px';
      shell.style.transform=`translateY(${ty.toFixed(2)}px) scale(${s.toFixed(4)})`;
      shell.style.borderWidth=`${(1/s).toFixed(2)}px`;
      shell.style.borderRadius=`${((14+34*e)/s).toFixed(1)}px`;
      shell.style.boxShadow=e>.05?`0 ${(3*e/s).toFixed(2)}px ${(14*e/s).toFixed(2)}px var(--shadow)`:'';
      shell.style.setProperty('--p',p.toFixed(4));
      shell.style.setProperty('--s',s.toFixed(4));
      ws.style.gridTemplateRows=`${(g.full*s+10*e).toFixed(1)}px minmax(0,1fr)`;
      shell.classList.toggle('folded',p>.73);
      shell.classList.add('folding');
    };

    const update=()=>{
      g.raf=0;
      if(g.p===0){g.h0=panel.clientHeight||g.h0;g.m0=panel.scrollHeight-g.h0}
      let p=0;
      if(isStacked()&&g.full&&g.h0>0&&g.m0>2){
        const anchor=panel.querySelector('.route-card');
        if(anchor){
          const sTop=panel.scrollTop;
          const aTop=anchor.getBoundingClientRect().top-panel.getBoundingClientRect().top+sTop;
          const rowH1=Math.min(g.full*.5,FOLD_CHIP_H)+10;
          const t1=Math.min(aTop-g.h0*.15,g.m0-(g.full-rowH1));
          if(t1>20){
            const t0=Math.max(0,Math.min(aTop-g.h0,t1-60));
            p=clamp01((sTop-t0)/(t1-t0));
          }
        }
      }
      if(p!==g.p)apply(p);
    };

    const schedule=()=>{ if(!g.raf)g.raf=requestAnimationFrame(update); };
    scheduleFold.current=schedule;

    const onResize=()=>{apply(0);measure();update()};
    measure(); update();
    panel.addEventListener('scroll',schedule,{passive:true});
    window.addEventListener('resize',onResize);
    return()=>{
      panel.removeEventListener('scroll',schedule);
      window.removeEventListener('resize',onResize);
      cancelAnimationFrame(g.raf); g.raf=0;
    };
  },[]);

  useEffect(()=>{ scheduleFold.current(); });

  useEffect(()=>{
    if(!model||!mapRef.current)return;
    markers.current.forEach(m=>m.remove()); markers.current.clear();
    model.stations.forEach(s=>{
      const color=LINE_COLORS[s.lines[0]]||'#666';
      const icon=L.divIcon({className:'station-dot',html:`<span style="--c:${color}"></span>`,iconSize:[16,16],iconAnchor:[8,8]});
      const m=L.marker([s.lat,s.lng],{icon}).addTo(mapRef.current).bindTooltip(s.fa,{direction:'top',offset:[0,-8],opacity:.98});
      m.on('click',()=>setDestination({lat:s.lat,lng:s.lng,stationId:s.id}));
      markers.current.set(s.id,m);
    });
  },[model]);

  useEffect(()=>{ markers.current.forEach(m=>showStations?m.addTo(mapRef.current):m.remove()); },[showStations]);

  const nearest=useMemo(()=>{
    if(!destination||!model)return null;
    if(destination.stationId){const station=model.byId.get(destination.stationId);return station?{station,distance:0}:null}
    let best=null;
    for(const s of model.stations){const d=haversine(destination,{lat:s.lat,lng:s.lng});if(!best||d<best.distance)best={station:s,distance:d}}
    return best;
  },[destination,model]);

  const results=useMemo(()=>{
    if(!model||!query)return [];
    const q=normalize(query);
    return model.stations.filter(s=>normalize(s.fa).includes(q)||normalize(s.name).includes(q)).slice(0,8);
  },[model,query]);

  function calculate(start,dest,mod,penalty){
    if(!start||!dest)return null;
    const target=dest.stationId?mod.byId.get(dest.stationId):nearest?.station;
    if(!target)return null;
    const r=shortestRoute(mod,start,target.id,penalty);
    return r?{...r,target,distance:haversine(dest,{lat:target.lat,lng:target.lng})}:{error:true};
  }

  useEffect(()=>{
    if(!mapRef.current||!destination)return;
    if(destMarker.current)destMarker.current.remove();
    const icon=L.divIcon({className:'destination-marker',html:'<span></span>',iconSize:[42,42],iconAnchor:[21,21]});
    destMarker.current=L.marker([destination.lat,destination.lng],{icon,zIndexOffset:1000}).addTo(mapRef.current).bindTooltip('مقصد',{direction:'top'}).openTooltip();
    mapRef.current.flyTo([destination.lat,destination.lng],Math.max(mapRef.current.getZoom(),13),{duration:.45});
    if(origin&&model)setRoute(calculate(origin,destination,model,transferPenalty));
  },[destination]);

  useEffect(()=>{ if(origin&&destination&&model)setRoute(calculate(origin,destination,model,transferPenalty)); },[origin,transferPenalty,nearest]);

  useEffect(()=>{
    if(!route?.stations||!model||!mapRef.current)return;
    routeLayer.current?.remove();
    const group=L.layerGroup().addTo(mapRef.current);
    routeLayer.current=group;
    const pts=route.stations.map(id=>{const s=model.byId.get(id);return [s.lat,s.lng]});
    const casing=document.documentElement.getAttribute('data-theme')==='light'?'#fbf1c7':'#1d2021';
    L.polyline(pts,{color:casing,weight:13,opacity:.7,lineCap:'round',lineJoin:'round'}).addTo(group);
    route.steps.forEach(step=>{
      const a=model.byId.get(step.from),b=model.byId.get(step.to);
      if(!a||!b)return;
      L.polyline([[a.lat,a.lng],[b.lat,b.lng]],{
        color:LINE_COLORS[step.line]||'#fe8019',weight:7,opacity:1,lineCap:'round'
      }).addTo(group);
    });
  },[route,model,theme]);

  const chooseOrigin=station=>{setOrigin(station.id);setQuery('');mapRef.current?.flyTo([station.lat,station.lng],13,{duration:.4})};
  const chooseDestination=station=>{setDestination({lat:station.lat,lng:station.lng,stationId:station.id});setQuery('')};
  const unfold=()=>panelRef.current?.scrollTo({top:0,behavior:'smooth'});
  const clearAll=()=>{setOrigin('');setQuery('');setDestination(null);setRoute(null);destMarker.current?.remove();routeLayer.current?.remove();unfold();};

  return <div className="app">
    <header className="topbar">
      <div className="brand-lockup">
        <div className="brand-mark" aria-hidden="true"><span>🚇</span></div>
        <div><div className="brand">مرتو</div><div className="tagline">مسیریابی متروی تهران، بدون پیچیدگی</div></div>
      </div>
      <button className="theme-toggle" onClick={()=>setTheme(t=>t==='light'?'dark':'light')} aria-label="تغییر حالت روشن و تیره">{theme==='light'?'🌕':'☀️'}</button>
      <button className="reset-button" onClick={clearAll}>شروع دوباره <b>↻</b></button>
    </header>

    <main className="workspace" ref={workspaceRef}>
      <section className="map-shell" ref={shellRef}>
        <div ref={mapEl} className="map" />
        <div className="map-overlay map-title"><span>تهران</span><strong>انتخاب مقصد</strong></div>
        <div className="map-overlay map-help">روی نقشه ضربه بزن · یا یک ایستگاه را انتخاب کن</div>
        <button className={`map-toggle ${showStations?'active':''}`} onClick={()=>setShowStations(v=>!v)}>{showStations?'● ایستگاه‌ها':'○ ایستگاه‌ها'}</button>
        {loading&&<div className="map-message">در حال دریافت شبکه…</div>}
        {error&&<div className="map-message error">{error}</div>}
        <button type="button" className="map-fold" onClick={unfold} aria-label="بازگشت به نقشه"><span>🗺️</span></button>
      </section>

      <aside className="panel" ref={panelRef}>
        <div className="panel-kicker">MERTO / v1</div>
        <h1>بریم؟</h1>
        <p className="intro">مبدأت را انتخاب کن، بعد هر نقطه‌ای از تهران را روی نقشه بزن.</p>

        <section className="field-block">
          <div className="field-caption"><span className="number">01</span><span>از کجا سوار می‌شی؟</span></div>
          <div className="search-box">
            <span className="search-icon">⌕</span>
            <input value={query} onChange={e=>setQuery(e.target.value)} placeholder="نام ایستگاه را بنویس…" aria-label="جستجوی ایستگاه مبدأ" />
            {query&&<button className="clear-search" onClick={()=>setQuery('')} aria-label="پاک کردن">×</button>}
          </div>
          {query&&<div className="results">{results.length?results.map(s=><button key={s.id} onClick={()=>chooseOrigin(s)}><span className="station-name">{s.fa}</span><span className="line-list">{s.lines.map(l=><i key={l} style={{background:LINE_COLORS[l]}}>{l}</i>)}</span></button>):<div className="no-results">ایستگاهی با این نام پیدا نشد.</div>}</div>}
          <div className={`selected-station ${origin?'selected':''}`}>
            <span className="selected-icon">{origin?'✅':'➕'}</span>
            <span>{origin?model?.byId.get(origin)?.fa:'هنوز مبدأ انتخاب نشده'}</span>
          </div>
        </section>

        <section className="field-block destination-block">
          <div className="field-caption"><span className="number">02</span><span>کجا می‌خوای بری؟</span></div>
          <div className={`destination-box ${destination?'has-destination':''}`}>
            <span className="destination-icon">📍</span>
            <div><strong>{destination?'مقصد روی نقشه انتخاب شد':'روی نقشه یک نقطه انتخاب کن'}</strong><small>{destination?'حالا نزدیک‌ترین ایستگاه را پیدا می‌کنیم':'می‌توانی مستقیماً روی یک ایستگاه هم بزنی'}</small></div>
          </div>
        </section>

        {nearest&&<section className="nearest-card">
          <div><span>نزدیک‌ترین ایستگاه</span><strong>{nearest.station.fa}</strong></div>
          <b>{nearest.distance===0?'همین‌جاست':fmtDistance(nearest.distance)}</b>
        </section>}

        {!origin&&!destination&&<div className="empty-card"><span>🚉</span><div><strong>مسیرت اینجا ظاهر می‌شه</strong><small>مبدأ + مقصد را انتخاب کن تا حرکت کنیم.</small></div></div>}
        {destination&&!origin&&<div className="tip-card"><span>→</span><div><strong>حالا مبدأ را انتخاب کن</strong><small>از کادر بالا نام ایستگاه را جست‌وجو کن.</small></div></div>}
        {origin&&destination&&route?.error&&<div className="tip-card danger"><span>!</span><div><strong>مسیر پیدا نشد</strong><small>برای این دو ایستگاه اتصال مستقیمی در داده‌ی شبکه پیدا نشد.</small></div></div>}

        {route&&!route.error&&<section className="route-card">
          <div className="route-head" style={{backgroundImage:routeGradient(route)}}><div><span>مسیر پیشنهادی</span><strong>{route.target.fa}</strong></div><div className="route-badge">{route.transfers?`${route.transfers} تعویض`:'بدون تعویض'}</div></div>
          <div className="route-stats"><span><b>{route.stations.length-1}</b> ایستگاه</span><span><b>≈ {Math.max(3,Math.round((route.stations.length-1)*2.4+route.transfers*4))}</b> دقیقه</span></div>
          <div className="route-line">
            {route.steps.map((step,i)=>{
              const to=model.byId.get(step.to);
              return <React.Fragment key={i}>
                {i>0&&step.changed&&<div className="transfer-pill" style={{'--line':LINE_COLORS[step.line]||'#555'}}><span>تعویض به خط {step.line}</span></div>}
                <div className="route-step" style={{'--line':LINE_COLORS[step.line]||'#555'}}>
                  <div className="step-marker"><span>{step.line}</span></div>
                  <div className="step-content"><small>خط {step.line}</small><strong>{to.fa}</strong></div>
                </div>
              </React.Fragment>;
            })}
          </div>
          <div className="arrival"><span>آخر مسیر</span><strong>{route.target.fa}</strong><small>{route.distance<80?'مقصد کنار ایستگاه است':`${fmtDistance(route.distance)} تا مقصد`}</small></div>
        </section>}

        <details className="advanced"><summary>تنظیمات مسیر</summary><label>اهمیت تعویض خط <input type="range" min="0" max="12" value={transferPenalty} onChange={e=>setTransferPenalty(+e.target.value)}/></label></details>
        <footer><span>مرتو</span> · داده‌های شبکه از منبع عمومی ایستگاه‌ها · نقشه: OpenStreetMap</footer>
      </aside>
    </main>
  </div>;
}

createRoot(document.getElementById('root')).render(<App/>);
