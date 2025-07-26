#include <iostream>
#include <vector>
#include <algorithm>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <set>
#include <queue>
#include <stack>
#include <cmath>
#include <string>
#include <deque>
#include <tuple>
#include <iomanip>
#include <climits>
#include <cstdint>
#include <functional>
using namespace std;
typedef long long ll;
typedef unsigned long long llu;
const ll INFLL = (long long)1e18;
const ll INF = 1e9+7;
const ll MOD = 1e9+7;
using Graph = vector<vector<ll>>;
using WeightedGraph = vector<vector<pair<ll, ll>>>;

#define vll vector<ll>
#define vll2d vector<vector<ll>>
#define vllu vector<llu>
#define vllu2d vector<vector<llu>>
#define pll pair<ll, ll>
#define vpll vector<pll>
#define YES cout << "YES\n"
#define NO cout << "NO\n"
#define FOR(i, start, upperbound, step) for (ll i = start; i < upperbound; i += step)
#define READVEC(v, n) FOR(i, 0, n, 1) { cin >> v[i]; }
#define BEGEND(x) x.begin(), x.end()
#define REVBEGEND(x) x.rbegin(), x.rend()

namespace modArithmetic{
	ll mod_add(ll a, ll b) { return (a + b) % MOD; }
	ll mod_sub(ll a, ll b) { return (a - b + MOD) % MOD; }
	ll mod_mul(ll a, ll b) { return (a * b) % MOD; }
	ll mod_pow(ll a, ll b) {
		ll res = 1;
		while (b) {
			if (b & 1) res = mod_mul(res, a);
			a = mod_mul(a, a);
			b >>= 1;
		}
		return res;
	}
}
using namespace modArithmetic;

namespace graphs{
	void dfs(ll node, const Graph& graph, vector<bool>& visited) {
		visited[node] = true;
		for (ll neighbor : graph[node]) {
			if (!visited[neighbor]) {
				dfs(neighbor, graph, visited);
			}
		}
	}
	
	//startpoint, edge list, returns {previous, cost} 
	void bfs(ll startpoint, Graph& graph, vector<pair<ll, ll>>& result) {
		result = vector<pair<ll,ll>>(graph.size(), pair(-1,-1));
		vector<bool> visited(graph.size());
		queue<ll> q;
		visited[startpoint] = true;
		result[startpoint] = {-1, 0};
		q.push(startpoint);

		while (!q.empty()) {
			ll u = q.front(); q.pop();

			for (ll v : graph[u]) {
				if (visited[v]) continue;
				visited[v] = true;
				result[v] = {u, result[u].second + 1};
				q.push(v);
			}
		}
	}

	//startpoint, for eachvertex an edge list: {second vertex, weight}, returns {previous, cost} 
	void Dijkstra(ll startpoint, const WeightedGraph& graph, vector<pair<ll, ll>>& result){
		ll n = graph.size();
		result = vector<pair<ll,ll>>(n, pair(-1ll, INFLL));
		result[startpoint] = {-1, 0};
		
		vector<bool> visited(n, false);
		priority_queue<pair<ll, ll>, vector<pair<ll, ll>>, greater<pair<ll, ll>>> dist;
		dist.push(make_pair(0ll, startpoint));
		
		while (dist.size()){
			ll u = dist.top().second;
			ll dist_u = dist.top().first;
			dist.pop();
			if (visited[u]) continue;

			visited[u] = true;
			for (auto [v, w] : graph[u]){
				if (visited[v]) continue;
				ll newDist = dist_u + w;
				if (newDist < result[v].second){
					result[v] = {u, newDist};
					dist.push({newDist, v});
				}
			}
		}
	}

	//startpoint, for eachvertex an edge list: {second vertex, weight}, returns {previous, cost} 
	int BellmanFord(ll startpoint, const WeightedGraph& graph, vector<pair<ll, ll>>& result){
		ll n = graph.size();
		result = vector<pair<ll, ll>>(n, { -1, INFLL });
		result[startpoint] = { -1, 0 };

		for (ll i = 0; i < n - 1; i++) {
			for (ll u = 0; u < n; u++) {
				if (result[u].second == INFLL) continue;
				for (auto [v, w] : graph[u]) {
					if (result[u].second + w < result[v].second) {
						result[v] = { u, result[u].second + w };
					}
				}
			}
		}

		// Check for negative cycles
		for (ll u = 0; u < n; u++) {
			if (result[u].second == INFLL) continue;
			for (auto [v, w] : graph[u]) {
				if (result[u].second + w < result[v].second) {
					return 1;
				}
			}
		}

		return 0;
	}

	struct Edge {
		ll w; ll u; ll v;
		Edge(ll _w, ll _u, ll _v) : w(_w), u(_u), v(_v) {}
		bool operator<(const Edge& oths) const{
			return w < oths.w;
		}
	};

	struct DSU{
		vector<ll> parent, size;

		DSU(ll n) : parent(n), size(n, 1) {
			for (ll i = 0; i < n; i++) parent[i] = i;
		}

		ll find(ll v) {
			if (parent[v] != v) parent[v] = find(parent[v]);
			return parent[v];
		}

		void merge(ll v, ll u) {
			ll rootV = find(v);
			ll rootU = find(u);
			if (rootV == rootU) return;
			if (size[rootV] < size[rootU]) swap(rootV, rootU);
			parent[rootU] = rootV;
			size[rootV] += size[rootU];
		}
	};

	//edges of the graph, result
	void Kruskal(ll n, vector<Edge>& graph, vector<Edge>& result){
		sort(graph.begin(), graph.end());
		DSU dsu(n);
		for (const Edge& e : graph) {
			if (dsu.find(e.v) != dsu.find(e.u)) {
				dsu.merge(e.v, e.u);
				result.push_back(e);
				if (result.size() == (size_t)n - 1) break;
			}
		}
	}

	void Kruskal(const WeightedGraph& graph, vector<Edge>& result){
		vector<Edge> edges;
		ll n = graph.size();
		for (ll u = 0; u < n; u++){
			for (auto [v, w] : graph[u]){
				edges.push_back(Edge(w, u, v));
			}
		}
		Kruskal(n, edges, result);
	}

	void FFbuildAdj(Graph& matrix, Graph& adj){
		adj = Graph(matrix.size());
		for (ll u = 0; (size_t)u < matrix.size(); ++u) {
			for (ll v = 0; (size_t)v < matrix[u].size(); ++v) {
				if (matrix[u][v] > 0) {
					adj[u].push_back(v);
					adj[v].push_back(u);
				}
			}
		}
	}
	
	bool FFbfs(ll source, ll sink, Graph& capacities, Graph& adj, Graph& flow, vector<pair<ll, ll>>& reversedRoute){
		vector<bool> visited(capacities.size());
		queue<ll> q;
		q.push(source);
		visited[source] = true;
		
		vector<ll> parent(capacities.size(), -1ll);

		bool found = false;
		while (!q.empty()){
			ll u = q.front(); q.pop();
			if (u == sink){
				found = true;
				break;
			}

			for (ll v : adj[u]) {
				if (visited[v]) continue;
				
				if (flow[u][v] < capacities[u][v]){
					visited[v] = true;
					parent[v] = u;
					q.push(v);
				}
				else if (flow[v][u] > 0){
					visited[v] = true;
					parent[v] = u;
					q.push(v);
				}
			}
		}

		if (!found){
			return false;
		}

		reversedRoute.clear();
		for (ll v = sink; v != source; v = parent[v]){
			reversedRoute.emplace_back(parent[v], v);
		}
		//reverse(route.begin(), route.end());
		
		return true;
	}

	//the stratpoint, and the graph[u][v] = capacity, 0 = no edge. assumes matrix.
	ll FordFulkerson(ll source, ll sink, Graph& capacities, Graph& flow){
		flow = Graph(capacities.size(), vector<ll>(capacities.size(), 0));
		
		Graph adj;
		FFbuildAdj(capacities, adj);
		
		vector<pair<ll, ll>> route; 

		ll maxflow = 0;
		while (FFbfs(source, sink, capacities, adj, flow, route)){
			ll delta = INF;
			for (auto [u, v] : route) {
				ll d;
				if (flow[u][v] < capacities[u][v]) d = capacities[u][v] - flow[u][v]; // forward edge
				else d = flow[v][u]; // backward edge
			    delta = min(delta, d);
			}

			for (auto [u, v] : route) {
				if (flow[u][v] < capacities[u][v]) {
					//forwards edge
					flow[u][v] = flow[u][v] + delta;
				}
				else {
					//backwards edge
					flow[v][u] = flow[v][u] - delta;
				}
			}
			maxflow += delta;
		}
		
		return maxflow;
	}

	vector<ll> getRoute(ll target, const vector<pair<ll,ll>>& result) {
		vector<ll> route;
		while (target != -1) {
			route.push_back(target);
			target = result[target].first;
		}
		reverse(route.begin(), route.end());
		return route;
	}

	ll getRouteLength(ll target, const vector<pair<ll,ll>>& result) {
		ll len = 0;
		while (target != -1) {
			len++;
			target = result[target].first;
		}
		return len;
	}
}
using namespace graphs;

//⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣿⣶⣄⣀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
//⠀⠀⠀⠀⠀⠀⠀⢀⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⣶⣦⣄⣀⡀⣠⣾⡇⠀⠀⠀⠀
//⠀⠀⠀⠀⠀⠀⣴⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡇⠀⠀⠀⠀
//⠀⠀⠀⠀⢀⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠿⠿⢿⣿⣿⡇⠀⠀⠀⠀
//⠀⣶⣿⣦⣜⣿⣿⣿⡟⠻⣿⣿⣿⣿⣿⣿⣿⡿⢿⡏⣴⣺⣦⣙⣿⣷⣄⠀⠀⠀
//⠀⣯⡇⣻⣿⣿⣿⣿⣷⣾⣿⣬⣥⣭⣽⣿⣿⣧⣼⡇⣯⣇⣹⣿⣿⣿⣿⣧⠀⠀
//⠀⠹⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠸⣿⣿⣿⣿⣿⣿⣿⣷⠀

void solution(){
	
}	

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
	int t = 1; 
	//cin >> t; //uncomment if multiple tests
	while (t--){
		solution();
	}
	cout << endl;
	return 0;
}
