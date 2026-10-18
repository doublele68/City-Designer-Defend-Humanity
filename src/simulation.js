/* Flood Lab — deterministic finite-volume toy model, world units are game units. */
(function(root){
'use strict';
const N=28, BUDGET=2000, DT=1/30, DURATION=64;
const LEVELS=[null,
 {name:'入门涨水',desc:'认识高低地：别把普通住宅全放在低处',peak:9,duration:56,targetSaved:64,centerHP:1},
 {name:'协同防洪',desc:'组合住房、堤墙、蓄洪与泵站，建立完整防线',peak:23,duration:64,targetSaved:90,centerHP:20},
 {name:'持续暴雨',desc:'保护供电核心，兼顾蓄洪容量与退水',peak:27,duration:68,targetSaved:108,centerHP:35},
 {name:'极端洪峰',desc:'有限预算下，处理漫顶与断电连锁',peak:31,duration:72,targetSaved:133,centerHP:50},
 {name:'韧性极限',desc:'精确布置防线与排水，几乎不容许住宅损失',peak:34,duration:76,targetSaved:152,centerHP:60}
];
const EVENT_TIME=12;
const TYPES={
 house:{name:'普通住宅',cost:60,pop:10,threshold:.34,color:0xf2e6cb,desc:'10 位居民 · 经济实惠，浅水也需防护'},
 stilt:{name:'高脚住宅',cost:110,pop:6,threshold:.85,color:0xe7cf9b,desc:'6 位居民 · 架空防淹，但容量更小、单位住房更贵'},
 center:{name:'应急中心',cost:180,pop:0,threshold:.42,color:0xe78054,desc:'保护目标 · 为 6 格内的泵站供电'},
 wall:{name:'堤墙',cost:22,pop:0,threshold:0,color:0xa0b5bb,desc:'阻挡与引导水流 · 长时间漫顶会溃决'},
 basin:{name:'蓄洪池',cost:50,pop:0,threshold:99,color:0x537d70,desc:'收集邻近低地积水到地下蓄水舱 · 容量 14 m³，满后停止吸纳'},
 pump:{name:'泵站',cost:100,pop:0,threshold:1.15,color:0x70adad,desc:'排出周围积水 · 必须在应急中心 6 格内供电'}
};
const idx=(x,z)=>z*N+x;
function river(z){return 8.4+Math.sin(z*.21)*2.2;}
function terrain(){const a=new Float64Array(N*N);for(let z=0;z<N;z++)for(let x=0;x<N;x++){
 const d=Math.abs(x-river(z));let h;
 if(d<2)h=-.65+(N-z)*.012;
 else if(d<3.1)h=-.24+(N-z)*.012;
 else {
  h=.32+(N-z)*.015+.12*Math.sin(x*.55)+.10*Math.cos(z*.62);
  h+=1.05*Math.exp(-((x-20)**2+(z-8)**2)/4.2);
  h+=.75*Math.exp(-((x-18)**2/2.8+(z-13)**2/6));
  h+=.9*Math.exp(-((x-22)**2+(z-18)**2)/2.7);
  h-=.30*Math.exp(-((x-15)**2+(z-17)**2)/7);
  if(x>24)h+=(x-24)*.22;if(x<3)h+=(3-x)*.20;
  h=Math.max(.24,Math.round(h/.12)*.12);
 }
 a[idx(x,z)]=h;
}return a;}
function starter(){const b=[];let id=1;const put=(type,x,z)=>b.push({id:id++,type,x,z});
 put('center',17,13);for(const [x,z] of [[14,8],[16,8],[18,8],[14,10],[18,10],[14,15],[16,16],[18,16]])put('house',x,z);
 put('stilt',20,12);put('stilt',20,15);put('pump',15,13);put('basin',12,18);
 for(let z=8;z<17;z++)put('wall',12,z);
 return b;
}
function buildable(type,x,z){return type==='wall'||type==='basin'||(x>=12&&x<=23&&z>=6&&z<=20);}
function clone(a){return JSON.parse(JSON.stringify(a));}
function cost(a){return a.reduce((s,b)=>s+(TYPES[b.type]?.cost||0),0);}
function population(a){return a.reduce((s,b)=>s+(TYPES[b.type]?.pop||0),0);}
function randomBias(rng=Math.random){return (rng()+rng()-1)*.1;}
function validate(layout){if(!Array.isArray(layout)||layout.length>N*N)return false;const cells=new Set(), ids=new Set();return layout.every(b=>{const key=idx(b.x,b.z);if(!TYPES[b.type]||!Number.isInteger(b.x)||!Number.isInteger(b.z)||b.x<0||b.z<0||b.x>=N||b.z>=N||cells.has(key)||ids.has(b.id)||!Number.isInteger(b.id))return false;cells.add(key);ids.add(b.id);return true;})&&cost(layout)<=BUDGET;}
class Simulation{
 constructor(layout,level=2,bias=0){this.base=terrain();this.ground=this.base.slice();this.water=new Float64Array(N*N);this.peak=new Float64Array(N*N);this.delta=new Float64Array(N*N);this.outgoing=new Float64Array(N*N);this.fluxX=new Float64Array(N*N);this.fluxZ=new Float64Array(N*N);this.flowX=new Float64Array(N*N);this.flowZ=new Float64Array(N*N);this.buildings=clone(layout).map(b=>({...b,hp:100,dead:false,powered:false,wet:false,stored:0}));this.level=level;this.config=LEVELS[level];this.duration=this.config.duration;this.bias=Math.max(-.1,Math.min(.1,bias));this.eventTriggered=false;this.time=0;this.events=[];this.ended=false;this.input=0;this.output=0;this.pumped=0;
 for(const b of this.buildings){const i=idx(b.x,b.z);if(b.type==='wall')this.ground[i]+=1.5;if(b.type==='basin')this.ground[i]-=1.2;}
 for(let i=0;i<N*N;i++){if(this.base[i]<.2)this.water[i]=Math.max(0,.06-this.ground[i]);}
 this.initialVolume=this.volume();this.intakesDirty=true;this.updatePower(false);
 }
 volume(){return this.water.reduce((a,b)=>a+b,0);}
 event(text,b,kind='danger'){this.events.push({time:this.time,text,x:b?.x,z:b?.z,kind});}
 updatePower(emit=true){const centers=this.buildings.filter(b=>b.type==='center'&&!b.dead);for(const b of this.buildings)if(b.type==='pump'){const on=!b.dead&&centers.some(c=>Math.hypot(c.x-b.x,c.z-b.z)<=6);if(emit&&b.powered&&!on)this.event('泵站断电，保护区停止排水',b);b.powered=on;}}
 refreshIntakes(){const walls=new Set(this.buildings.filter(b=>b.type==='wall'&&!b.dead).map(b=>idx(b.x,b.z)));for(const b of this.buildings)if(b.type==='pump'){const found=new Set([idx(b.x,b.z)]),queue=[[b.x,b.z]];for(let k=0;k<queue.length;k++){const [x,z]=queue[k];for(const [nx,nz] of [[x-1,z],[x+1,z],[x,z-1],[x,z+1]]){const j=idx(nx,nz);if(nx<0||nx>=N||nz<0||nz>=N||Math.hypot(nx-b.x,nz-b.z)>2.5||walls.has(j)||found.has(j))continue;found.add(j);queue.push([nx,nz]);}}b.intake=[...found];}this.intakesDirty=false;}
 step(dt=DT){if(this.ended)return;dt=Math.min(dt,DT);this.time+=dt;
 // One random factor scales the entire hydrograph. Replays are otherwise deterministic.
 if(!this.eventTriggered&&this.time>=EVENT_TIME){this.eventTriggered=true;const amount=(Math.abs(this.bias)*100).toFixed(1);this.event(this.bias>=0?'伴随降雨，洪水量增加 '+amount+'%':'上游雨势减弱，洪水量减少 '+amount+'%',null,'weather');}
 const floodEnd=this.duration-12,phase=Math.min(1,this.time/floodEnd);
 const pulse=this.time<floodEnd?Math.pow(Math.sin(Math.PI*phase),.8):0;
 const rate=this.config.peak*pulse*(1+(this.eventTriggered?this.bias:0));
 for(let x=0;x<N;x++)if(Math.abs(x-river(0))<2){const v=rate*dt/4;this.water[idx(x,0)]+=v;this.input+=v;}
 this.delta.fill(0);this.outgoing.fill(0);this.fluxX.fill(0);this.fluxZ.fill(0);this.flowX.fill(0);this.flowZ.fill(0);
 const edge=(i,j,arr)=>{const hi=this.ground[i]+this.water[i],hj=this.ground[j]+this.water[j];const high=hi>hj?i:j,low=high===i?j:i;const head=Math.max(0,(high===i?hi:hj)-Math.max(this.ground[low],high===i?hj:hi));const f=Math.min(20,head*3.8)*dt;arr[i]=(high===i?1:-1)*f;this.outgoing[high]+=f;};
 for(let z=0;z<N;z++)for(let x=0;x<N;x++){const i=idx(x,z);if(x<N-1)edge(i,i+1,this.fluxX);if(z<N-1)edge(i,i+N,this.fluxZ);}
 const transfer=(i,j,f,flow)=>{const from=f>=0?i:j,to=f>=0?j:i;const q=Math.abs(f)*Math.min(1,this.water[from]/(this.outgoing[from]||1));this.delta[from]-=q;this.delta[to]+=q;flow[i]=Math.sign(f)*q/dt;};
 for(let z=0;z<N;z++)for(let x=0;x<N;x++){const i=idx(x,z);if(x<N-1)transfer(i,i+1,this.fluxX[i],this.flowX);if(z<N-1)transfer(i,i+N,this.fluxZ[i],this.flowZ);}
 for(let i=0;i<N*N;i++)this.water[i]=Math.max(0,this.water[i]+this.delta[i]);
 // Only the visible downstream edge is an outlet. No hidden side drains.
 for(let x=0;x<N;x++){const i=idx(x,N-1),q=Math.min(this.water[i],Math.max(0,this.ground[i]+this.water[i]-.06)*2.5*dt);this.water[i]-=q;this.output+=q;}
 this.updatePower();if(this.intakesDirty)this.refreshIntakes();
 for(const b of this.buildings){if(b.dead)continue;const i=idx(b.x,b.z),d=this.water[i];
 if(b.type==='basin'&&b.stored<14){let room=Math.min(14-b.stored,1.4*dt);const cells=[];for(let z=Math.max(0,b.z-1);z<=Math.min(N-1,b.z+1);z++)for(let x=Math.max(0,b.x-1);x<=Math.min(N-1,b.x+1);x++){const j=idx(x,z);if(this.ground[j]<=this.base[i]+.3&&!this.buildings.some(c=>c.type==='wall'&&!c.dead&&c.x===x&&c.z===z))cells.push(j);}cells.sort((a,c)=>this.water[c]-this.water[a]);for(const j of cells){const q=Math.min(room,this.water[j]);this.water[j]-=q;b.stored+=q;room-=q;if(room<=0)break;}}
 if(b.type==='pump'&&b.powered){let remaining=.85*dt;const cells=b.intake.slice();cells.sort((a,c)=>this.water[c]-this.water[a]);for(const j of cells){const q=Math.min(remaining,this.water[j]);this.water[j]-=q;remaining-=q;this.pumped+=q;if(remaining<=0)break;}}
 if(b.type==='wall'){if(d>.035){b.hp-=dt*(7+d*16);if(!b.wet){b.wet=true;this.event('堤墙开始漫顶，持续冲刷会形成溃口',b,'warning');}}}
 else if(b.type!=='basin'){const excess=d-TYPES[b.type].threshold;if(excess>0){b.hp-=dt*(4+excess*25);if(!b.wet){b.wet=true;this.event(TYPES[b.type].name+'进水，持续浸泡将失效',b,'warning');}}}
 if(b.hp<=0){b.hp=0;b.dead=true;if(b.type==='wall'){this.ground[i]=this.base[i]+.12;this.intakesDirty=true;this.event('堤墙溃决，洪水从缺口涌入',b);}else this.event(b.type==='center'?'应急中心失效，附近泵站失去电源':TYPES[b.type].name+'被洪水摧毁',b);}
 }
 this.updatePower();for(let i=0;i<N*N;i++)this.peak[i]=Math.max(this.peak[i],this.water[i]);if(this.time>=this.duration){this.time=this.duration;this.ended=true;}
 }
 result(){const pop=population(this.buildings),saved=this.buildings.reduce((s,b)=>s+(b.dead?0:TYPES[b.type].pop),0),centers=this.buildings.filter(b=>b.type==='center'),centerAlive=centers.length>0&&centers.every(b=>!b.dead),centerHealth=centers.length?Math.min(...centers.map(b=>b.hp)):0,centerOK=centerAlive&&centerHealth>=this.config.centerHP,passed=saved>=this.config.targetSaved&&centerOK,lost=pop-saved,score=saved,survival=pop?saved/pop:0,extra=Math.max(0,saved-this.config.targetSaved),zeroLoss=pop>0&&lost===0;return {pop,saved,lost,score,survival,extra,zeroLoss,targetSaved:this.config.targetSaved,centerOK,centerAlive,centerHealth,passed,level:this.level,bias:this.bias,spent:cost(this.buildings),destroyed:this.buildings.filter(b=>b.dead).length};}
}
function replayAtTime(layout,level,bias,time){const s=new Simulation(layout,level,bias);while(!s.ended&&s.time+1e-7<time)s.step();return s;}
function compareResults(a,b){return a.saved-b.saved||b.lost-a.lost;}
function unlockedLevel(passed){let n=1;while(n<5&&passed.includes(n))n++;return n;}
root.Flood={compareResults,replayAtTime,unlockedLevel,N,BUDGET,DT,DURATION,LEVELS,EVENT_TIME,TYPES,idx,river,terrain,starter,buildable,clone,cost,population,randomBias,validate,Simulation};
if(typeof module!=='undefined')module.exports=root.Flood;
})(typeof window!=='undefined'?window:globalThis);
