#include <bits/stdc++.h>
using namespace std;

using ll = long long;
const ll INF = (1LL << 60);

struct DSU {
    vector<int> p, r;
    DSU(int n=0) { init(n); }
    void init(int n) { p.resize(n); r.assign(n,0); iota(p.begin(),p.end(),0); }
    int find(int x){ return p[x]==x?x:p[x]=find(p[x]); }
    bool unite(int a,int b){
        a=find(a); b=find(b); if(a==b) return false;
        if(r[a]<r[b]) swap(a,b);
        p[b]=a;
        if(r[a]==r[b]) r[a]++;
        return true;
    }
};

struct Edge {
    int to, rev;
    ll cap, original;
};

class EdmondsKarp {
public:
    vector<vector<Edge>> g;
    explicit EdmondsKarp(int n): g(n) {}

    int addEdge(int u, int v, ll cap) {
        Edge a{v, (int)g[v].size(), cap, cap};
        Edge b{u, (int)g[u].size(), 0, 0};
        g[u].push_back(a); g[v].push_back(b);
        return (int)g[u].size()-1;
    }

    ll maxflow(int s, int t) {
        ll flow=0;
        while(true){
            vector<int> pv(g.size(), -1), pe(g.size(), -1);
            queue<int> q; q.push(s); pv[s]=s;
            while(!q.empty() && pv[t]==-1){
                int u=q.front(); q.pop();
                for(int i=0;i<(int)g[u].size();++i){
                    if(pv[g[u][i].to]==-1 && g[u][i].cap>0){
                        pv[g[u][i].to]=u; pe[g[u][i].to]=i;
                        q.push(g[u][i].to);
                        if(g[u][i].to==t) break;
                    }
                }
            }
            if(pv[t]==-1) break;
            ll add=INF;
            for(int v=t; v!=s; v=pv[v]) add=min(add, g[pv[v]][pe[v]].cap);
            for(int v=t; v!=s; v=pv[v]){
                Edge &e=g[pv[v]][pe[v]];
                e.cap-=add; g[v][e.rev].cap+=add;
            }
            flow+=add;
        }
        return flow;
    }
};

struct Zone {
    int node;
    int weight, volume, hazard, value, risk;
    int start, finish;
};
struct Hub { int node; ll fixedCost, capacity; };
struct Plant { int node; ll capacity; };
struct Vehicle { int wcap, vcap, hcap, start, finish; };

struct HubChoice {
    vector<int> hubs;
    ll potential=-1;
    ll estimatedCost=INF;
};

// Algorithm 1: Floyd-Warshall all-pairs shortest path.
void floydWarshall(vector<vector<ll>>& d){
    int n=d.size();
    for(int k=0;k<n;k++)
        for(int i=0;i<n;i++) if(d[i][k]<INF)
            for(int j=0;j<n;j++) if(d[k][j]<INF && d[i][k] <= INF-d[k][j])
                d[i][j]=min(d[i][j], d[i][k]+d[k][j]);
}

HubChoice chooseHubs(const vector<Zone>& zones, const vector<Hub>& hubs,
                     const vector<Plant>& plants, const vector<vector<ll>>& d,
                     int K, ll budget){
    int p=hubs.size();
    if(p>20) throw runtime_error("This academic exhaustive hub selector requires P <= 20.");
    ll totalGen=0, totalPlant=0;
    for(auto &z:zones) totalGen+=z.weight;
    for(auto &r:plants) totalPlant+=r.capacity;

    HubChoice best;
    for(int mask=1; mask<(1<<p); ++mask){
        if(__builtin_popcount((unsigned)mask)>K) continue;
        ll fixed=0, hubCap=0;
        vector<int> selected;
        for(int i=0;i<p;i++) if(mask>>i&1){
            fixed += hubs[i].fixedCost;
            hubCap += hubs[i].capacity;
            selected.push_back(i);
        }
        if(fixed>budget) continue;

        bool feasible=true;
        ll transport=0;
        for(auto &z:zones){
            ll bestPath=INF;
            for(int hi:selected){
                if(d[z.node][hubs[hi].node]>=INF) continue;
                for(auto &r:plants){
                    if(d[hubs[hi].node][r.node]>=INF) continue;
                    bestPath=min(bestPath, d[z.node][hubs[hi].node]+d[hubs[hi].node][r.node]);
                }
            }
            if(bestPath>=INF){ feasible=false; break; }
            if(z.weight>0 && bestPath > (INF-fixed-transport)/max(1,z.weight)) { feasible=false; break; }
            transport += bestPath * z.weight;
        }
        if(!feasible) continue;
        ll potential=min(totalGen, min(hubCap, totalPlant));
        ll cost=fixed+transport;
        if(potential>best.potential ||
           (potential==best.potential && cost<best.estimatedCost) ||
           (potential==best.potential && cost==best.estimatedCost && selected<best.hubs)){
            best={selected,potential,cost};
        }
    }
    return best;
}

// Algorithm 2: Kruskal MST on the metric closure of selected hubs + central plant.
pair<ll, vector<tuple<int,int,ll>>> kruskalBackbone(const vector<int>& selected,
        const vector<Hub>& hubs, int centralNode, const vector<vector<ll>>& d){
    vector<int> nodes;
    for(int hi:selected) nodes.push_back(hubs[hi].node);
    nodes.push_back(centralNode);
    int n=nodes.size();
    vector<tuple<ll,int,int>> edges;
    for(int i=0;i<n;i++) for(int j=i+1;j<n;j++) if(d[nodes[i]][nodes[j]]<INF)
        edges.emplace_back(d[nodes[i]][nodes[j]], i, j);
    sort(edges.begin(),edges.end());
    DSU dsu(n); ll cost=0; vector<tuple<int,int,ll>> used;
    for(auto [w,a,b]:edges){
        if(dsu.unite(a,b)){
            cost+=w; used.emplace_back(nodes[a],nodes[b],w);
            if((int)used.size()==n-1) break;
        }
    }
    if((int)used.size()!=n-1) return {INF,{}};
    return {cost,used};
}

struct FlowResult { ll maxFlow; vector<ll> zoneFlow; };

// Algorithm 3: Edmonds-Karp max-flow / min-cut.
FlowResult formalThroughput(const vector<Zone>& zones, const vector<Hub>& hubs,
                            const vector<int>& selected, const vector<Plant>& plants,
                            const vector<vector<ll>>& d){
    int Z=zones.size(), H=selected.size(), R=plants.size();
    int S=0;
    int zoneBase=1;
    int hubInBase=zoneBase+Z;
    int hubOutBase=hubInBase+H;
    int plantBase=hubOutBase+H;
    int T=plantBase+R;
    EdmondsKarp mf(T+1);
    vector<pair<int,int>> srcEdge(Z);
    ll total=0;
    for(int i=0;i<Z;i++){
        int idx=mf.addEdge(S, zoneBase+i, zones[i].weight);
        srcEdge[i]={S,idx}; total+=zones[i].weight;
    }
    for(int i=0;i<Z;i++) for(int j=0;j<H;j++){
        const Hub &h=hubs[selected[j]];
        if(d[zones[i].node][h.node]<INF) mf.addEdge(zoneBase+i, hubInBase+j, zones[i].weight);
    }
    for(int j=0;j<H;j++) mf.addEdge(hubInBase+j, hubOutBase+j, hubs[selected[j]].capacity);
    for(int j=0;j<H;j++) for(int r=0;r<R;r++)
        if(d[hubs[selected[j]].node][plants[r].node]<INF)
            mf.addEdge(hubOutBase+j, plantBase+r, total);
    for(int r=0;r<R;r++) mf.addEdge(plantBase+r, T, plants[r].capacity);

    ll f=mf.maxflow(S,T);
    vector<ll> zf(Z,0);
    for(int i=0;i<Z;i++){
        auto [u,idx]=srcEdge[i];
        const Edge &e=mf.g[u][idx];
        zf[i]=e.original-e.cap;
    }
    return {f,zf};
}

struct LoadState {
    int value=-1;
    vector<int> picked;
};

static string key3(int a,int b,int c){ return to_string(a)+","+to_string(b)+","+to_string(c); }
static tuple<int,int,int> parse3(const string& s){
    size_t p1=s.find(','), p2=s.find(',',p1+1);
    return {stoi(s.substr(0,p1)), stoi(s.substr(p1+1,p2-p1-1)), stoi(s.substr(p2+1))};
}

// Algorithm 4: sparse multi-dimensional 0/1 knapsack DP.
pair<int,vector<int>> knapsackVehicle(const Vehicle& veh, const vector<Zone>& zones,
                                      const vector<int>& candidates){
    unordered_map<string,LoadState> dp;
    dp[key3(0,0,0)]={0,{}};
    for(int zi:candidates){
        auto next=dp;
        for(auto &kv:dp){
            auto [w,v,h]=parse3(kv.first);
            int nw=w+zones[zi].weight, nv=v+zones[zi].volume, nh=h+zones[zi].hazard;
            if(nw>veh.wcap || nv>veh.vcap || nh>veh.hcap) continue;
            string nk=key3(nw,nv,nh);
            int nval=kv.second.value+zones[zi].value;
            auto it=next.find(nk);
            vector<int> np=kv.second.picked; np.push_back(zi);
            if(it==next.end() || nval>it->second.value || (nval==it->second.value && np<it->second.picked))
                next[nk]={nval,np};
        }
        dp.swap(next);
    }
    LoadState best{0,{}};
    for(auto &kv:dp){
        if(kv.second.value>best.value ||
           (kv.second.value==best.value && kv.second.picked<best.picked)) best=kv.second;
    }
    return {best.value,best.picked};
}

// Algorithm 5: classic earliest-finish-time greedy interval scheduling.
vector<int> intervalSchedule(const vector<int>& items, const vector<Zone>& zones,
                             int dayStart, int dayFinish){
    vector<int> a;
    for(int i:items) if(zones[i].start>=dayStart && zones[i].finish<=dayFinish) a.push_back(i);
    sort(a.begin(),a.end(),[&](int x,int y){
        if(zones[x].finish!=zones[y].finish) return zones[x].finish<zones[y].finish;
        if(zones[x].start!=zones[y].start) return zones[x].start<zones[y].start;
        return x<y;
    });
    vector<int> ans; int last=dayStart;
    for(int i:a){ if(zones[i].start>=last){ ans.push_back(i); last=zones[i].finish; } }
    return ans;
}

// Reservoir sample k items from one stratum; explicit RNG makes tests reproducible.
vector<int> reservoirSample(const vector<int>& a, int k, mt19937& rng){
    k=min(k,(int)a.size());
    vector<int> res;
    for(int i=0;i<(int)a.size();i++){
        if(i<k) res.push_back(a[i]);
        else {
            uniform_int_distribution<int> dist(0,i);
            int j=dist(rng);
            if(j<k) res[j]=a[i];
        }
    }
    sort(res.begin(),res.end());
    return res;
}

// Algorithm 6: stratified + reservoir randomized audit sampling.
vector<int> stratifiedAuditSample(const vector<Zone>& zones, int quota, unsigned seed){
    vector<vector<int>> strata(3); // low <40, medium 40..69, high >=70
    for(int i=0;i<(int)zones.size();i++){
        int s=(zones[i].risk>=70?2:(zones[i].risk>=40?1:0));
        strata[s].push_back(i);
    }
    quota=min(quota,(int)zones.size());
    vector<int> q(3,0);
    int nonempty=0; for(auto &s:strata) if(!s.empty()) nonempty++;
    int remaining=quota;
    if(quota>=nonempty){
        for(int s=0;s<3;s++) if(!strata[s].empty()){ q[s]=1; remaining--; }
    }
    int total=zones.size();
    vector<pair<double,int>> rem;
    for(int s=0;s<3;s++){
        if(strata[s].empty()) continue;
        double ideal=(double)quota*strata[s].size()/max(1,total);
        int extra=min((int)strata[s].size()-q[s], (int)floor(max(0.0, ideal-q[s])));
        q[s]+=extra; remaining-=extra;
        rem.push_back({ideal-floor(ideal),s});
    }
    sort(rem.begin(),rem.end(),[](auto a, auto b){
        if(a.first!=b.first) return a.first>b.first;
        return a.second>b.second; // high risk first only for tie in leftover allocation
    });
    while(remaining>0){
        bool moved=false;
        for(auto [frac,s]:rem){
            if(q[s]<(int)strata[s].size() && remaining>0){ q[s]++; remaining--; moved=true; }
        }
        if(!moved) break;
    }
    mt19937 rng(seed);
    vector<int> sample;
    for(int s=0;s<3;s++){
        auto part=reservoirSample(strata[s],q[s],rng);
        sample.insert(sample.end(),part.begin(),part.end());
    }
    sort(sample.begin(),sample.end());
    return sample;
}

vector<int> scheduleAudits(vector<int> sampled, const vector<Zone>& zones, int inspectors){
    vector<int> scheduled, remaining=sampled;
    for(int day=0; day<inspectors && !remaining.empty(); ++day){
        vector<int> picked=intervalSchedule(remaining,zones,0,24);
        unordered_set<int> used(picked.begin(),picked.end());
        scheduled.insert(scheduled.end(),picked.begin(),picked.end());
        vector<int> nr; for(int z:remaining) if(!used.count(z)) nr.push_back(z);
        remaining.swap(nr);
    }
    sort(scheduled.begin(),scheduled.end());
    return scheduled;
}

string list1Based(const vector<int>& a){
    if(a.empty()) return "none";
    string s;
    for(int i=0;i<(int)a.size();i++){ if(i) s+=' '; s+=to_string(a[i]+1); }
    return s;
}

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    int T; if(!(cin>>T)) return 0;
    for(int tc=1; tc<=T; ++tc){
        int N,M; cin>>N>>M;
        vector<vector<ll>> d(N,vector<ll>(N,INF));
        for(int i=0;i<N;i++) d[i][i]=0;
        for(int i=0;i<M;i++){
            int u,v; ll w; cin>>u>>v>>w; --u;--v;
            d[u][v]=min(d[u][v],w); d[v][u]=min(d[v][u],w);
        }
        int Z,P,R; cin>>Z>>P>>R;
        vector<Zone> zones(Z);
        for(auto &z:zones){ cin>>z.node>>z.weight>>z.volume>>z.hazard>>z.value>>z.risk>>z.start>>z.finish; --z.node; }
        vector<Hub> hubs(P);
        for(auto &h:hubs){ cin>>h.node>>h.fixedCost>>h.capacity; --h.node; }
        vector<Plant> plants(R);
        for(auto &r:plants){ cin>>r.node>>r.capacity; --r.node; }
        int K, centralPlantIndex; ll budget; cin>>K>>budget>>centralPlantIndex; --centralPlantIndex;
        int V; cin>>V;
        vector<Vehicle> vehicles(V);
        for(auto &v:vehicles) cin>>v.wcap>>v.vcap>>v.hcap>>v.start>>v.finish;
        int inspectors,auditQuota; unsigned seed; cin>>inspectors>>auditQuota>>seed;

        floydWarshall(d);
        HubChoice choice=chooseHubs(zones,hubs,plants,d,K,budget);
        cout<<"Case "<<tc<<"\n";
        if(choice.hubs.empty()){
            cout<<"No feasible hub subset under the given budget/connectivity constraints.\n";
            if(tc<T) cout<<"\n";
            continue;
        }
        cout<<"Selected hubs: "<<list1Based(choice.hubs)<<"\n";
        cout<<"Hub-selection potential throughput: "<<choice.potential<<"\n";
        cout<<"Estimated hub+transport cost: "<<choice.estimatedCost<<"\n";

        int centralNode=plants[centralPlantIndex].node;
        auto [mstCost,mstEdges]=kruskalBackbone(choice.hubs,hubs,centralNode,d);
        if(mstCost>=INF) cout<<"Backbone MST: disconnected\n";
        else cout<<"Backbone MST cost: "<<mstCost<<"\n";

        FlowResult fr=formalThroughput(zones,hubs,choice.hubs,plants,d);
        cout<<"Maximum formal throughput: "<<fr.maxFlow<<"\n";

        vector<int> available;
        for(int i=0;i<Z;i++) if(fr.zoneFlow[i]>0) available.push_back(i);
        for(int vi=0; vi<V; ++vi){
            auto [val,picked]=knapsackVehicle(vehicles[vi],zones,available);
            vector<int> sched=intervalSchedule(picked,zones,vehicles[vi].start,vehicles[vi].finish);
            cout<<"Vehicle "<<vi+1<<" load value: "<<val<<"; picked zones: "<<list1Based(picked)
                <<"; scheduled zones: "<<list1Based(sched)<<"\n";
            unordered_set<int> used(sched.begin(),sched.end());
            vector<int> next;
            for(int z:available) if(!used.count(z)) next.push_back(z);
            available.swap(next);
        }

        vector<int> audits=stratifiedAuditSample(zones,auditQuota,seed);
        vector<int> auditSchedule=scheduleAudits(audits,zones,inspectors);
        cout<<"Randomized audit sample: "<<list1Based(audits)<<"\n";
        cout<<"Scheduled audits: "<<list1Based(auditSchedule)<<"\n";
        if(tc<T) cout<<"\n";
    }
}
