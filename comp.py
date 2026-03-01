import argparse
import json
import copy
import math
import sys



class HashIndex:
    
    def __init__(self, relation_name, attr, pages, schema):
        self.relation = relation_name
        self.attr = attr
        self.index = {}
        col = schema.index(attr)
        
        
        for pi, page in enumerate(pages):
            for ri, row in enumerate(page):
                val = row[col]
                key = str(val)
                
                if key not in self.index:
                    self.index[key] = []
                self.index[key].append((pi, ri))

    def lookup(self, val):
        key = str(val)
        matches = self.index.get(key, [])
        pages_touched = set(pi for pi, ri in matches)
        
        return matches, pages_touched


def attr_relation(attr):
    return attr.split(".")[0]

def attr_field(attr):
    return attr.split(".")[1]

def relations_in_node(node):
    if node["op"] == "Scan":
        return {node["relation"]}
    rels = set()
    
    for key in ("child", "left", "right"):
        if key in node:
            rels |= relations_in_node(node[key])
    return rels



class Optimizer:
    def __init__(self, relations_data, stats):
        self.page_size = relations_data["page_size"]
        self.relations = relations_data["relations"]
        self.stats = stats
        self.indexes = {}
        
        index_specs = [("Student", "major"), ("Student", "sid"), ("Enroll", "sid")]
        
        for rel, attr in index_specs:
            if rel in self.relations:
                r = self.relations[rel]
                idx = HashIndex(rel, attr, r["pages"], r["schema"])
                self.indexes[(rel, attr)] = idx

    def rewrite(self, plan):
        plan = copy.deepcopy(plan)
        plan = self._push_selections_down(plan)
        plan = self._combine_selections(plan)
        plan = self._push_projections_down(plan)
        return plan

    def _push_selections_down(self, node):
        if node["op"] == "Select" and "child" in node:
            child = node["child"]
            if child["op"] == "Join":
                pred_rel = attr_relation(node["predicate"][0])
                left_rels = relations_in_node(child["left"])
                right_rels = relations_in_node(child["right"])
                if pred_rel in left_rels:
                    child["left"] = {"op": "Select", "predicate": node["predicate"],
                                     "child": child["left"]}
                    return self._push_selections_down(child)
                
                elif pred_rel in right_rels:
                    child["right"] = {"op": "Select", "predicate": node["predicate"],
                                      "child": child["right"]}
                    
                    return self._push_selections_down(child)

        for key in ("child", "left", "right"):
            if key in node:
                node[key] = self._push_selections_down(node[key])
        return node

    def _combine_selections(self, node):
        if node["op"] == "Select" and "child" in node:
            node["child"] = self._combine_selections(node["child"])
            
            if node["child"]["op"] == "Select":
                inner = node["child"]
                combined = node["predicate"] + ["AND"] + inner["predicate"]
                
                return {"op": "Select", "predicate": combined, "child": inner["child"]}
            
        for key in ("child", "left", "right"):
            
            if key in node:
                node[key] = self._combine_selections(node[key])
                
        return node

    def _push_projections_down(self, node):
        for key in ("child", "left", "right"):
            if key in node:
                
                node[key] = self._push_projections_down(node[key])
                
        return node

    def estimate_card(self, node):
        op = node["op"]
        if op == "Scan":
            rel = node["relation"]
            return self.stats[rel]["T"]
        
        elif op == "Select":
            
            child_card = self.estimate_card(node["child"])
            preds = self._split_predicates(node["predicate"])
            card = child_card
            
            for attr, _, val in preds:
                rel = attr_relation(attr)
                field = attr_field(attr)
                v = self.stats[rel]["V"].get(field, 1)
                card = card / v
                
            return max(1, math.ceil(card))
        
        elif op == "Join":
            left_card = self.estimate_card(node["left"])
            right_card = self.estimate_card(node["right"])
            
            cond = node["condition"]
            left_attr = cond[0]
            right_attr = cond[2]
            
            l_rel = attr_relation(left_attr)
            l_field = attr_field(left_attr)
            r_rel = attr_relation(right_attr)
            r_field = attr_field(right_attr)
            
            v_left = self.stats[l_rel]["V"].get(l_field, 1)
            v_right = self.stats[r_rel]["V"].get(r_field, 1)
            
            card = (left_card * right_card) / max(v_left, v_right)
            
            return max(1, math.ceil(card))
        
        elif op == "Project":
            return self.estimate_card(node["child"])
        return 1

    def estimate_pages(self, node):
        return max(1, math.ceil(self.estimate_card(node) / self.page_size))

    def _split_predicates(self, pred):
        parts = []
        i = 0
        
        while i < len(pred):
            parts.append((pred[i], pred[i + 1], pred[i + 2]))
            i += 3
            
            if i < len(pred) and pred[i] == "AND":
                i += 1
        return parts

    def enumerate_plans(self, logical):
        op = logical["op"]

        if op == "Scan":
            rel = logical["relation"]
            
            return [{"phys_op": "SeqScan", "relation": rel, "filter": None}]

        elif op == "Select":
            child = logical["child"]
            preds = self._split_predicates(logical["predicate"])

            if child["op"] == "Scan":
                rel = child["relation"]
                plans = []
                plans.append({
                    "phys_op": "SeqScan", "relation": rel,
                    "filter": logical["predicate"]
                })
                for attr, _, val in preds:
                    field = attr_field(attr)
                    r = attr_relation(attr)
                    if (r, field) in self.indexes:
                        plans.append({
                            "phys_op": "IndexScan", "relation": rel,
                            "attr": field, "val": val,
                            "filter": logical["predicate"]
                        })
                        break
                return plans
            
            else:
                child_plans = self.enumerate_plans(child)
                results = []
                
                for cp in child_plans:
                    results.append({
                        "phys_op": "Filter",
                        "filter": logical["predicate"],
                        "child": cp
                    })
                return results

        elif op == "Join":
            left_plans = self.enumerate_plans(logical["left"])
            right_plans = self.enumerate_plans(logical["right"])
            cond = logical["condition"]
            plans = []

            for lp in left_plans:
                for rp in right_plans:
                    plans.append({
                        "phys_op": "HashJoin", "condition": cond,
                        "left": copy.deepcopy(lp), "right": copy.deepcopy(rp)
                    })
                    
                    plans.append({
                        "phys_op": "NLJ", "condition": cond,
                        "outer": copy.deepcopy(lp), "inner": copy.deepcopy(rp)
                    })
                    
                    plans.append({
                        "phys_op": "NLJ", "condition": cond,
                        "outer": copy.deepcopy(rp), "inner": copy.deepcopy(lp)
                    })

            return plans

        elif op == "Project":
            child_plans = self.enumerate_plans(logical["child"])
            return [{
                "phys_op": "Project", "attrs": logical["attrs"],
                "child": cp
            } for cp in child_plans]

        return []


    def cost(self, phys):
        op = phys["phys_op"]

        if op == "SeqScan":
            rel = phys["relation"]
            return self.stats[rel]["B"]

        elif op == "IndexScan":
            rel = phys["relation"]
            attr = phys["attr"]
            lookup_cost = 1
            
            t = self.stats[rel]["T"]
            v = self.stats[rel]["V"].get(attr, 1)
            est_tuples = t / v
            page_cost = math.ceil(est_tuples / self.page_size)
            
            return lookup_cost + page_cost

        elif op == "HashJoin":
            return self.cost(phys["left"]) + self.cost(phys["right"])

        elif op == "NLJ":
            outer_cost = self.cost(phys["outer"])
            outer_tuples = self._est_tuples_phys(phys["outer"])
            inner_cost = self.cost(phys["inner"])
            return outer_cost + outer_tuples * inner_cost

        elif op == "Project":
            return self.cost(phys["child"])

        elif op == "Filter":
            return self.cost(phys["child"])

        return 0

    def _est_tuples_phys(self, phys):
        op = phys["phys_op"]
        
        if op == "SeqScan":
            rel = phys["relation"]
            
            if phys.get("filter"):
                preds = self._split_predicates(phys["filter"])
                card = self.stats[rel]["T"]
                
                for attr, _, val in preds:
                    r = attr_relation(attr)
                    f = attr_field(attr)
                    v = self.stats[r]["V"].get(f, 1)
                    card = card / v
                return max(1, math.ceil(card))
            
            return self.stats[rel]["T"]
        
        elif op == "IndexScan":
            rel = phys["relation"]
            attr = phys["attr"]
            t = self.stats[rel]["T"]
            v = self.stats[rel]["V"].get(attr, 1)
            est = t / v
            
            if phys.get("filter"):
                preds = self._split_predicates(phys["filter"])
                for a, _, val in preds:
                    f = attr_field(a)
                    if f != attr:
                        v2 = self.stats[rel]["V"].get(f, 1)
                        est = est / v2
            return max(1, math.ceil(est))
        
        elif op == "HashJoin":
            lt = self._est_tuples_phys(phys["left"])
            rt = self._est_tuples_phys(phys["right"])
            cond = phys["condition"]
            l_rel = attr_relation(cond[0])
            l_f = attr_field(cond[0])
            r_rel = attr_relation(cond[2])
            r_f = attr_field(cond[2])
            v = max(self.stats[l_rel]["V"].get(l_f, 1),
                    self.stats[r_rel]["V"].get(r_f, 1))
            
            return max(1, math.ceil((lt * rt) / v))
        
        elif op == "NLJ":
            ot = self._est_tuples_phys(phys["outer"])
            it = self._est_tuples_phys(phys["inner"])
            cond = phys["condition"]
            l_rel = attr_relation(cond[0])
            l_f = attr_field(cond[0])
            r_rel = attr_relation(cond[2])
            r_f = attr_field(cond[2])
            v = max(self.stats[l_rel]["V"].get(l_f, 1),
                    self.stats[r_rel]["V"].get(r_f, 1))
            
            return max(1, math.ceil((ot * it) / v))
        elif op == "Project":
            
            return self._est_tuples_phys(phys["child"])
        elif op == "Filter":
            
            child_tuples = self._est_tuples_phys(phys["child"])
            preds = self._split_predicates(phys["filter"])
            card = child_tuples
            
            for attr, _, val in preds:
                r = attr_relation(attr)
                f = attr_field(attr)
                v = self.stats[r]["V"].get(f, 1)
                card = card / v
            return max(1, math.ceil(card))
        return 1

    def _est_pages_phys(self, phys):
        return max(1, math.ceil(self._est_tuples_phys(phys) / self.page_size))

    def execute(self, phys):
        op = phys["phys_op"]

        if op == "SeqScan":
            return self._exec_seqscan(phys)
        elif op == "IndexScan":
            return self._exec_indexscan(phys)
        elif op == "HashJoin":
            return self._exec_hashjoin(phys)
        elif op == "NLJ":
            return self._exec_nlj(phys)
        elif op == "Project":
            return self._exec_project(phys)
        elif op == "Filter":
            return self._exec_filter(phys)
        
        return [], 0

    def _make_tuple(self, rel, row):
        schema = self.relations[rel]["schema"]
        return {f"{rel}.{col}": val for col, val in zip(schema, row)}

    def _exec_seqscan(self, phys):
        rel = phys["relation"]
        pages = self.relations[rel]["pages"]
        io = 0
        results = []
        
        for page in pages:
            io += 1
            for row in page:
                t = self._make_tuple(rel, row)
                if phys.get("filter"):
                    if self._eval_filter(t, phys["filter"]):
                        results.append(t)
                else:
                    results.append(t)
        return results, io

    def _exec_indexscan(self, phys):
        rel = phys["relation"]
        attr = phys["attr"]
        val = phys["val"]
        idx = self.indexes[(rel, attr)]
        matches, pages_touched = idx.lookup(val)
        io = 1
        pages_data = self.relations[rel]["pages"]
        results = []
        
        for pi in sorted(pages_touched):
            io += 1
            
            for row in pages_data[pi]:
                t = self._make_tuple(rel, row)

                if phys.get("filter"):
                    if self._eval_filter(t, phys["filter"]):
                        results.append(t)
                else:
                    if str(t[f"{rel}.{attr}"]) == str(val):
                        results.append(t)
                        
        return results, io

    def _exec_hashjoin(self, phys):
        left_tuples, left_io = self.execute(phys["left"])
        right_tuples, right_io = self.execute(phys["right"])
        cond = phys["condition"]
        l_attr = cond[0]
        r_attr = cond[2]
        ht = {}
        
        for t in left_tuples:
            key = str(t.get(l_attr, ""))
            
            if key not in ht:
                ht[key] = []
            ht[key].append(t)

        results = []
        
        for rt in right_tuples:
            key = str(rt.get(r_attr, ""))
            
            if key in ht:
                
                for lt in ht[key]:
                    merged = {**lt, **rt}
                    results.append(merged)
                    
        return results, left_io + right_io

    def _exec_nlj(self, phys):
        outer_tuples, outer_io = self.execute(phys["outer"])
        cond = phys["condition"]
        l_attr = cond[0]
        r_attr = cond[2]
        total_io = outer_io
        results = []
        
        for ot in outer_tuples:
            inner_tuples, inner_io = self.execute(phys["inner"])
            total_io += inner_io
            
            for it in inner_tuples:
                if l_attr in ot and r_attr in it:
                    
                    if str(ot[l_attr]) == str(it[r_attr]):
                        results.append({**ot, **it})
                        
                elif r_attr in ot and l_attr in it:
                    
                    if str(ot[r_attr]) == str(it[l_attr]):
                        results.append({**ot, **it})
                        
        return results, total_io

    def _exec_project(self, phys):
        tuples, io = self.execute(phys["child"])
        results = []
        
        for t in tuples:
            projected = {a: t[a] for a in phys["attrs"] if a in t}
            results.append(projected)
            
        return results, io

    def _exec_filter(self, phys):
        
        tuples, io = self.execute(phys["child"])
        results = [t for t in tuples if self._eval_filter(t, phys["filter"])]
        
        return results, io

    def _eval_filter(self, tup, predicate):
        preds = self._split_predicates(predicate)
        
        for attr, op, val in preds:
            actual = tup.get(attr)
            
            if actual is None:
                return False
            if op == "=":
                if str(actual) != str(val):
                    
                    return False
        return True

    def _plan_description(self, phys, indent=0):
        pad = "  " * indent
        op = phys["phys_op"]
        
        if op == "SeqScan":
            filt = ""
            
            if phys.get("filter"):
                filt = f" [filter: {phys['filter']}]"
                
            return f"{pad}SeqScan({phys['relation']}){filt}"
        
        elif op == "IndexScan":
            return f"{pad}IndexScan({phys['relation']}.{phys['attr']}={phys['val']})"
        
        elif op == "HashJoin":
            left = self._plan_description(phys["left"], indent + 1)
            right = self._plan_description(phys["right"], indent + 1)
            return f"{pad}HashJoin({phys['condition']})\n{left}\n{right}"
        
        elif op == "NLJ":
            outer = self._plan_description(phys["outer"], indent + 1)
            inner = self._plan_description(phys["inner"], indent + 1)
            return f"{pad}NLJ({phys['condition']})\n{outer}\n{inner}"
        
        elif op == "Project":
            child = self._plan_description(phys["child"], indent + 1)
            return f"{pad}Project({phys['attrs']})\n{child}"
        
        elif op == "Filter":
            child = self._plan_description(phys["child"], indent + 1)
            return f"{pad}Filter({phys['filter']})\n{child}"
        
        return f"{pad}{op}"

    def _print_cardinalities(self, node, indent=0):
        pad = "  " * indent
        card = self.estimate_card(node)
        op = node["op"]
        
        if op == "Scan":
            print(f"{pad}Scan({node['relation']}) → {card} tuples")
        elif op == "Select":
            print(f"{pad}Select({node['predicate']}) → {card} tuples")
            self._print_cardinalities(node["child"], indent + 1)
        elif op == "Join":
            print(f"{pad}Join({node['condition']}) → {card} tuples")
            self._print_cardinalities(node["left"], indent + 1)
            self._print_cardinalities(node["right"], indent + 1)
        elif op == "Project":
            print(f"{pad}Project({node['attrs']}) → {card} tuples")
            self._print_cardinalities(node["child"], indent + 1)


    def run_query(self, query, idx):
        print(f"Query {idx}")

        print("\nOG")
        print(json.dumps(query, indent=2))

        rewritten = self.rewrite(query)
        print("\nrewritten")
        print(json.dumps(rewritten, indent=2))

        print("\n-card est")
        self._print_cardinalities(rewritten)

        phys_plans = self.enumerate_plans(rewritten)
        print(f"\n phys. plan ({len(phys_plans)} ")
        
        for i, pp in enumerate(phys_plans):
            
            c = self.cost(pp)
            print(f"  Plan {i+1}: est cost = {c}")
            desc = self._plan_description(pp, indent=2)
            print(desc)
            print()

        best = min(phys_plans, key=lambda p: self.cost(p))
        best_cost = self.cost(best)
        
        print(f"chosen Plan est cost = {best_cost}) --")
        print(self._plan_description(best, indent=1))

        result_tuples, actual_io = self.execute(best)
        print(f"\nActual exec")
        print(f"Actual I/O: {actual_io} pages")

        print(f"\nRes ({len(result_tuples)} tuples")
        for t in result_tuples:
            print(f"  {t}")

        print()


def load_queries(path):

    with open(path) as f:
        text = f.read().strip()

    try:
        parsed = json.loads(text)
        if isinstance(parsed, list):
            return parsed
        else:
            return [parsed]
    except json.JSONDecodeError:
        pass

    chunks = [c.strip() for c in text.split("\n\n") if c.strip()]
    
    if len(chunks) > 1:
        try:
            return [json.loads(c) for c in chunks]
        except json.JSONDecodeError:
            pass

    queries = []
    for line in text.splitlines():
        
        line = line.strip()
        
        if line:
            try:
                queries.append(json.loads(line))
            except json.JSONDecodeError:
                continue
    return queries



def main():
    parser = argparse.ArgumentParser(description="lab3")
    parser.add_argument("--relations", required=True, help=" relations path")
    parser.add_argument("--stats", required=True, help="statistics path")
    parser.add_argument("--queries", required=True, help="queries path")
    args = parser.parse_args()

    with open(args.relations) as f:
        relations_data = json.load(f)
        
    with open(args.stats) as f:
        stats = json.load(f)
    queries = load_queries(args.queries)

    opt = Optimizer(relations_data, stats)
    
    for i, q in enumerate(queries, 1):
        opt.run_query(q, i)


if __name__ == "__main__":
    main()
