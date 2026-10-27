module

public import CFSG.Quasithin.SteinbergBNA7Transvection
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.Quasithin.SteinbergBN

open SimpleGraph

section Graph

variable {I : Type*} {G : SimpleGraph I}

theorem mem_support_of_mem_support_drop {u v w : I} {p : G.Walk u v} {n : ℕ}
    (h : w ∈ (p.drop n).support) : w ∈ p.support := by
  rw [Walk.drop_support_eq_support_drop_min] at h
  exact List.mem_of_mem_drop h

theorem length_eq_one_of_adj_of_isPath (hG : G.IsAcyclic) {x y : I} (h : G.Adj x y)
    {q : G.Walk x y} (hq : q.IsPath) : q.length = 1 := by
  have e := (hG.subsingleton_path x y).elim ⟨q, hq⟩ (Path.singleton h)
  have := congrArg (fun r : G.Path x y => r.1.length) e
  simpa using this

theorem exists_subpath {u v : I} {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ p.length) :
    ∃ q : G.Walk (p.getVert i) (p.getVert j), q.IsPath ∧ q.length = j - i ∧
      ∀ w ∈ q.support, w ∈ p.support := by
  have he : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert, Nat.add_sub_cancel' hij]
  refine ⟨((p.drop i).take (j - i)).copy rfl he, ?_, ?_, ?_⟩
  · rw [Walk.isPath_copy]
    exact (hp.drop i).take (j - i)
  · rw [Walk.length_copy, Walk.take_length, Walk.drop_length]
    omega
  · intro w hw
    rw [Walk.support_copy, Walk.support_take] at hw
    exact mem_support_of_mem_support_drop (List.mem_of_mem_take hw)

theorem adj_getVert_iff (hG : G.IsAcyclic) {u v : I} {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  have key : ∀ {i j : ℕ}, i + 2 ≤ j → j ≤ p.length → ¬ G.Adj (p.getVert i) (p.getVert j) := by
    intro i j hij hj h
    obtain ⟨q, hq, hlen, -⟩ := exists_subpath hp (by omega : i ≤ j) hj
    have := length_eq_one_of_adj_of_isPath hG h hq
    omega
  constructor
  · intro h
    by_contra hne
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact key (by omega) hj h
    · subst heq
      exact G.irrefl h
    · exact key (by omega) hi h.symm
  · rintro (h | h)
    · subst h
      exact p.adj_getVert_succ (by omega)
    · subst h
      exact (p.adj_getVert_succ (by omega)).symm

theorem eq_of_adj_getVert_of_not_mem (hG : G.IsAcyclic) {u v : I} {p : G.Walk u v}
    (hp : p.IsPath) {w : I} (hw : w ∉ p.support) {i j : ℕ} (hi : i ≤ p.length)
    (hj : j ≤ p.length) (hwi : G.Adj w (p.getVert i)) (hwj : G.Adj w (p.getVert j)) : i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi hwj hwi (by omega)).symm
  by_contra hne
  obtain ⟨q, hq, hlen, hsupp⟩ := exists_subpath hp hij hj
  have hq' : (Walk.cons hwi q).IsPath :=
    (Walk.cons_isPath_iff hwi q).2 ⟨hq, fun h => hw (hsupp w h)⟩
  have := length_eq_one_of_adj_of_isPath hG hwj hq'
  rw [Walk.length_cons] at this
  omega

theorem exists_longest_path [Finite I] [Nonempty I] :
    ∃ (u v : I) (p : G.Walk u v), p.IsPath ∧
      ∀ (u' v' : I) (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length := by
  have : Fintype I := Fintype.ofFinite I
  let S : Set ℕ := {L | ∃ (u v : I) (p : G.Walk u v), p.IsPath ∧ p.length = L}
  have hne : S.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty I›
    exact ⟨0, x, x, Walk.nil, Walk.IsPath.nil, rfl⟩
  have hbdd : BddAbove S := ⟨Fintype.card I, by
    rintro L ⟨u, v, p, hp, rfl⟩
    exact hp.length_lt.le⟩
  obtain ⟨u, v, p, hp, hL⟩ := Nat.sSup_mem hne hbdd
  refine ⟨u, v, p, hp, fun u' v' q hq => ?_⟩
  rw [hL]
  exact le_csSup hbdd ⟨u', v', q, hq, rfl⟩

section Longest

variable {u v : I} {p : G.Walk u v} (hp : p.IsPath)
  (hmax : ∀ (u' v' : I) (q : G.Walk u' v'), q.IsPath → q.length ≤ p.length)
include hp hmax

theorem not_adj_start_of_longest {w : I} (hw : w ∉ p.support) : ¬ G.Adj w u := by
  intro h
  have := hmax w v (Walk.cons h p) ((Walk.cons_isPath_iff h p).2 ⟨hp, hw⟩)
  rw [Walk.length_cons] at this
  omega

theorem eq_getVert_one_of_adj_start (hG : G.IsAcyclic) {z : I}
    (hz : G.Adj u z) : z = p.getVert 1 := by
  by_cases hzp : z ∈ p.support
  · obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hzp
    have hz' : G.Adj (p.getVert 0) (p.getVert j) := by
      rw [Walk.getVert_zero]
      exact hz
    have := (adj_getVert_iff hG hp (Nat.zero_le _) hj).1 hz'
    have hj1 : j = 1 := by omega
    rw [hj1]
  · exact absurd hz.symm (not_adj_start_of_longest hp hmax hzp)

theorem eq_of_adj_of_adj_getVert_one (hG : G.IsAcyclic) (hL : 1 ≤ p.length) {w : I}
    (hw : w ∉ p.support) (hw1 : G.Adj w (p.getVert 1)) {z : I} (hz : G.Adj w z) :
    z = p.getVert 1 := by
  by_contra hne
  by_cases hzp : z ∈ p.support
  · obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hzp
    have := eq_of_adj_getVert_of_not_mem hG hp hw hL hj hw1 hz
    exact hne (by rw [this])
  · have hq : (Walk.cons hz.symm (Walk.cons hw1 (p.drop 1))).IsPath := by
      refine (Walk.cons_isPath_iff _ _).2 ⟨(Walk.cons_isPath_iff _ _).2
        ⟨hp.drop 1, fun h => hw (mem_support_of_mem_support_drop h)⟩, ?_⟩
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨hz.ne.symm, fun h => hzp (mem_support_of_mem_support_drop h)⟩
    have := hmax _ _ _ hq
    simp only [Walk.length_cons, Walk.drop_length] at this
    omega

end Longest

theorem e6_embedding_of_adj (hG : G.IsAcyclic) {u v : I} {p : G.Walk u v} (hp : p.IsPath)
    {w : I} (hw : w ∉ p.support) {k : ℕ} (hk2 : 2 ≤ k) (hkL : k + 2 ≤ p.length)
    (hwk : G.Adj w (p.getVert k)) : Nonempty (e6Tree ↪g G) := by
  let f : Fin 6 → I := fun x => if (x : ℕ) = 5 then w else p.getVert (k - 2 + x)
  have hwj : ∀ j ≤ p.length, G.Adj w (p.getVert j) ↔ j = k := fun j hj =>
    ⟨fun h => eq_of_adj_getVert_of_not_mem hG hp hw hj (by omega) h hwk, fun h => h ▸ hwk⟩
  have hwne : ∀ j, w ≠ p.getVert j := fun j h => hw (h ▸ p.getVert_mem_support j)
  have hadj : ∀ x y : Fin 6, G.Adj (f x) (f y) ↔ e6Tree.Adj x y := by
    intro x y
    rw [e6Tree_adj_iff]
    have hx := x.isLt
    have hy := y.isLt
    dsimp only [f]
    by_cases hx5 : (x : ℕ) = 5 <;> by_cases hy5 : (y : ℕ) = 5
    · rw [ite_eq_left hx5, ite_eq_left hy5]
      simp only [G.irrefl, false_iff]
      omega
    · rw [ite_eq_left hx5, ite_eq_right hy5, hwj _ (by omega)]
      omega
    · rw [ite_eq_right hx5, ite_eq_left hy5, G.adj_comm, hwj _ (by omega)]
      omega
    · rw [ite_eq_right hx5, ite_eq_right hy5, adj_getVert_iff hG hp (by omega) (by omega)]
      omega
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx := x.isLt
    have hy := y.isLt
    dsimp only [f] at hxy
    by_cases hx5 : (x : ℕ) = 5 <;> by_cases hy5 : (y : ℕ) = 5
    · exact Fin.ext (hx5.trans hy5.symm)
    · rw [ite_eq_left hx5, ite_eq_right hy5] at hxy
      exact absurd hxy (hwne _)
    · rw [ite_eq_right hx5, ite_eq_left hy5] at hxy
      exact absurd hxy.symm (hwne _)
    · rw [ite_eq_right hx5, ite_eq_right hy5] at hxy
      have := hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) hxy
      exact Fin.ext (by omega)
  exact ⟨⟨⟨f, hinj⟩, fun {x y} => hadj x y⟩⟩

theorem mem_of_walk {S : Set I} (hS : ∀ z ∈ S, ∀ z', G.Adj z z' → z' ∈ S) {x y : I}
    (q : G.Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction q with
  | nil => exact hx
  | cons h _ ih => exact ih (hS _ hx _ h)

end Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}
  {I : Type*}

theorem eq_of_pairing_eq (hnd : β.Nondegenerate) {a : I → V}
    (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤) {x y : V}
    (h : ∀ j, β x (a j) = β y (a j)) : x = y := by
  have h0 : ∀ z, β (x - y) z = 0 := by
    intro z
    have hz : z ∈ Submodule.span (ZMod 2) (Set.range a) := hspan ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      rw [map_sub, LinearMap.sub_apply, h j, sub_self]
    | zero => exact map_zero _
    | add z z' _ _ hz hz' => rw [map_add, hz, hz', add_zero]
    | smul c z _ hz => rw [map_smul, hz, smul_zero]
  exact sub_eq_zero.1 (hnd.1 (x - y) h0)

theorem exists_ne_of_span_eq_top [Nontrivial V] (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {a : I → V} (ha0 : ∀ i, a i ≠ 0) (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤) :
    ∃ i j : I, i ≠ j := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hI : Nonempty I := by
    by_contra hI
    rw [not_nonempty_iff] at hI
    rw [Set.range_eq_empty a, Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨i⟩ := hI
  refine ha0 i (eq_of_pairing_eq hnd hspan fun j => ?_)
  rw [hcon i j, hβ.self_eq_zero, map_zero, LinearMap.zero_apply]

theorem e6_free_tree_reduces_to_path [Finite I] [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (hβ : β.IsAlt) (hnd : β.Nondegenerate) (a : I → V) (ha0 : ∀ i, a i ≠ 0)
    (hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤) (htree : (pairGraph hβ a).IsTree)
    (hE6 : IsEmpty (e6Tree ↪g pairGraph hβ a)) :
    ∃ (n : ℕ) (s : Fin n → I), 2 ≤ n ∧ Function.Injective s ∧
      (∀ i, i ∉ Set.range s → ∃ k, a i = a (s k)) ∧
      pairGraph hβ (a ∘ s) = SimpleGraph.pathGraph n ∧
      Submodule.span (ZMod 2) (Set.range (a ∘ s)) = ⊤ ∧
      Subgroup.closure (Set.range fun k => transv hβ (a (s k))) =
        Subgroup.closure (Set.range fun i => transv hβ (a i)) := by
  set G := pairGraph hβ a with hGdef
  have hG : G.IsAcyclic := htree.isAcyclic
  obtain ⟨x, y, hxy⟩ := exists_ne_of_span_eq_top hβ hnd ha0 hspan
  have : Nonempty I := ⟨x⟩
  obtain ⟨u, v, p, hp, hmax⟩ := exists_longest_path (G := G)
  have hL1 : 1 ≤ p.length := by
    obtain ⟨q, hq⟩ := (htree.connected.preconnected x y).exists_isPath
    have h1 := hmax x y q hq
    have h2 : q.length ≠ 0 := fun h0 => hxy (Walk.eq_of_length_eq_zero h0)
    omega
  have hp' : p.reverse.IsPath := hp.reverse
  have hmax' : ∀ (u' v' : I) (q : G.Walk u' v'), q.IsPath → q.length ≤ p.reverse.length := by
    intro u' v' q hq
    rw [Walk.length_reverse]
    exact hmax u' v' q hq
  have hL1' : 1 ≤ p.reverse.length := by rwa [Walk.length_reverse]
  have hmem' : ∀ w, w ∈ p.reverse.support ↔ w ∈ p.support := fun w => by
    rw [Walk.support_reverse, List.mem_reverse]
  have hrev1 : p.reverse.getVert 1 = p.getVert (p.length - 1) := by
    rw [Walk.getVert_reverse]
  have hpos : ∀ w, w ∉ p.support → ∀ k ≤ p.length, G.Adj w (p.getVert k) →
      k = 1 ∨ k = p.length - 1 := by
    intro w hw k hk hwk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [Walk.getVert_zero] at hwk
      exact not_adj_start_of_longest hp hmax hw hwk
    have hkL : k ≠ p.length := by
      rintro rfl
      rw [Walk.getVert_length] at hwk
      exact not_adj_start_of_longest hp' hmax' (fun h => hw ((hmem' w).1 h)) hwk
    by_contra hne
    exact hE6.false (e6_embedding_of_adj hG hp hw (k := k) (by omega) (by omega) hwk).some
  let S : Set I := {z | z ∈ p.support ∨ ∃ k ≤ p.length, G.Adj z (p.getVert k)}
  have hS : ∀ z ∈ S, ∀ z', G.Adj z z' → z' ∈ S := by
    rintro z (hz | ⟨k, hk, hzk⟩) z' hzz'
    · obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hz
      exact Or.inr ⟨j, hj, hzz'.symm⟩
    · by_cases hzp : z ∈ p.support
      · obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hzp
        exact Or.inr ⟨j, hj, hzz'.symm⟩
      left
      rcases hpos z hzp k hk hzk with rfl | rfl
      · rw [eq_of_adj_of_adj_getVert_one hp hmax hG hL1 hzp hzk hzz']
        exact p.getVert_mem_support 1
      · rw [← hrev1] at hzk
        have := eq_of_adj_of_adj_getVert_one hp' hmax' hG hL1'
          (fun h => hzp ((hmem' z).1 h)) hzk hzz'
        rw [this, hrev1]
        exact p.getVert_mem_support _
  have hall : ∀ z, z ∈ S := fun z => by
    obtain ⟨q⟩ := htree.connected.preconnected u z
    exact mem_of_walk hS q (Or.inl p.start_mem_support)
  have hrow : ∀ {w e : I}, (∀ j, G.Adj w j ↔ G.Adj e j) → a w = a e := fun {w e} h =>
    eq_of_pairing_eq hnd hspan fun j => zmod_two_eq_of_iff (h j)
  have hend : ∀ w, w ∉ p.support → a w = a u ∨ a w = a v := by
    intro w hw
    rcases hall w with h | ⟨k, hk, hwk⟩
    · exact absurd h hw
    rcases hpos w hw k hk hwk with rfl | rfl
    · left
      refine hrow fun j => ⟨fun h => ?_, fun h => ?_⟩
      · rw [eq_of_adj_of_adj_getVert_one hp hmax hG hL1 hw hwk h]
        have h0 := p.adj_getVert_succ (i := 0) (by omega)
        rwa [Walk.getVert_zero, zero_add] at h0
      · rw [eq_getVert_one_of_adj_start hp hmax hG h]
        exact hwk
    · right
      rw [← hrev1] at hwk
      have hw' : w ∉ p.reverse.support := fun h => hw ((hmem' w).1 h)
      refine hrow fun j => ⟨fun h => ?_, fun h => ?_⟩
      · rw [eq_of_adj_of_adj_getVert_one hp' hmax' hG hL1' hw' hwk h]
        have h0 := p.reverse.adj_getVert_succ (i := 0) (by omega)
        rwa [Walk.getVert_zero, zero_add] at h0
      · rw [eq_getVert_one_of_adj_start hp' hmax' hG h]
        exact hwk
  let s : Fin (p.length + 1) → I := fun k => p.getVert k
  have hs : ∀ i, ∃ k, a i = a (s k) := by
    intro i
    by_cases hi : i ∈ p.support
    · obtain ⟨j, rfl, hj⟩ := Walk.mem_support_iff_exists_getVert.1 hi
      exact ⟨⟨j, by omega⟩, rfl⟩
    · rcases hend i hi with h | h
      · exact ⟨0, by rw [h]; exact congrArg a (Walk.getVert_zero p).symm⟩
      · exact ⟨Fin.last _, by rw [h]; exact congrArg a (Walk.getVert_length p).symm⟩
  have hrange : Set.range (a ∘ s) = Set.range a := by
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨s k, rfl⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hs i
      exact ⟨k, hk.symm⟩
  refine ⟨p.length + 1, s, by omega, ?_, fun i _ => hs i, ?_, by rw [hrange, hspan], ?_⟩
  · intro k l hkl
    exact Fin.ext (hp.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) hkl)
  · ext k l
    rw [SimpleGraph.pathGraph_adj]
    exact adj_getVert_iff hG hp (by omega) (by omega)
  · congr 1
    apply le_antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨s k, rfl⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := hs i
      exact ⟨k, by simp only [hk]⟩

end CFSG.Quasithin.SteinbergBN
