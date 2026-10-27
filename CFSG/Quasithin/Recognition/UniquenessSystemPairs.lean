module

public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG.Quasithin.Asc94

open MulAction
open scoped Pointwise

universe u v

section StdSubgraph

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

@[expose] def stdSubgraph (Γ : SimpleGraph X) [GraphAction G Γ] (I : Subgroup G) (x y : X)
    (hxy : Γ.Adj x y) : Γ.Subgraph where
  verts := {v | ∃ i ∈ I, i • x = v ∨ i • y = v}
  Adj u v := ∃ i ∈ I, (i • x = u ∧ i • y = v) ∨ (i • x = v ∧ i • y = u)
  adj_sub := by
    rintro u v ⟨i, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (GraphAction.adj_smul i x y).mpr hxy
    · exact ((GraphAction.adj_smul i x y).mpr hxy).symm
  edge_vert := by
    rintro u v ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  symm := ⟨by
    rintro u v ⟨i, hi, h | h⟩
    · exact ⟨i, hi, Or.inr h⟩
    · exact ⟨i, hi, Or.inl h⟩⟩

theorem stdSubgraph_verts_eq {Γ : SimpleGraph X} [GraphAction G Γ] {I : Subgroup G} {x y : X}
    (hxy : Γ.Adj x y) {t : G} (ht : t ∈ I) (htx : t • x = y) :
    (stdSubgraph Γ I x y hxy).verts = (fun i : G => i • x) '' (I : Set G) := by
  ext v
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact ⟨i, hi, rfl⟩
    · exact ⟨i * t, I.mul_mem hi ht, by simp [mul_smul, htx]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, Or.inl rfl⟩

theorem stdSubgraph_edgeSet_eq {Γ : SimpleGraph X} [GraphAction G Γ] {I : Subgroup G} {x y : X}
    (hxy : Γ.Adj x y) :
    (stdSubgraph Γ I x y hxy).edgeSet = (fun i : G => s(i • x, i • y)) '' (I : Set G) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.Subgraph.mem_edgeSet]
    constructor
    · rintro ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨i, hi, rfl⟩
      · exact ⟨i, hi, Sym2.eq_swap⟩
    · rintro ⟨i, hi, he⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨i, hi, Or.inl ⟨h1, h2⟩⟩
      · exact ⟨i, hi, Or.inr ⟨h1, h2⟩⟩

end StdSubgraph

variable (Θ : Type u)

abbrev Pair : Type u := {z : Sym2 Θ // ¬ z.IsDiag}

variable {Θ}

@[expose] def pair (p q : Θ) (h : p ≠ q) : Pair Θ := ⟨s(p, q), by simpa using h⟩

@[simp] theorem pair_val (p q : Θ) (h : p ≠ q) : (pair p q h).1 = s(p, q) := rfl

theorem pair_eq_iff {p q r s : Θ} {h : p ≠ q} {h' : r ≠ s} :
    pair p q h = pair r s h' ↔ (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  rw [← Subtype.coe_inj, pair_val, pair_val, Sym2.eq_iff]

theorem pair_comm (p q : Θ) (h : p ≠ q) : pair p q h = pair q p h.symm :=
  Subtype.ext Sym2.eq_swap

theorem Pair.exists_eq (z : Pair Θ) : ∃ p q, ∃ h : p ≠ q, z = pair p q h := by
  obtain ⟨z, hz⟩ := z
  induction z using Sym2.ind with
  | _ p q => exact ⟨p, q, by simpa using hz, rfl⟩

theorem Pair.exists_eq_of_mem (z : Pair Θ) {p : Θ} (hp : p ∈ z.1) :
    ∃ q, ∃ h : p ≠ q, z = pair p q h := by
  obtain ⟨r, s, h, rfl⟩ := z.exists_eq
  rcases Sym2.mem_iff.mp hp with rfl | rfl
  · exact ⟨s, h, rfl⟩
  · exact ⟨r, h.symm, pair_comm _ _ _⟩

variable {G : Type v} [Group G] [MulAction G Θ]

instance : MulAction G (Pair Θ) where
  smul g z := ⟨z.1.map (g • ·), by rw [Sym2.isDiag_map (MulAction.injective g)]; exact z.2⟩
  one_smul z := Subtype.ext (by
    change z.1.map ((1 : G) • ·) = z.1
    simp)
  mul_smul g h z := Subtype.ext (by
    change z.1.map ((g * h) • ·) = (z.1.map (h • ·)).map (g • ·)
    rw [Sym2.map_map]
    congr 1
    funext p
    simp [mul_smul])

@[simp] theorem smul_val (g : G) (z : Pair Θ) : (g • z).1 = z.1.map (g • ·) := rfl

theorem smul_pair (g : G) (p q : Θ) (h : p ≠ q) :
    g • pair p q h = pair (g • p) (g • q) ((MulAction.injective g).ne h) :=
  Subtype.ext (by simp)

theorem mem_smul_iff (g : G) (z : Pair Θ) (p : Θ) : p ∈ (g • z).1 ↔ g⁻¹ • p ∈ z.1 := by
  obtain ⟨r, s, h, rfl⟩ := z.exists_eq
  simp only [smul_pair, pair_val, Sym2.mem_iff]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left; rw [← h]; simp
    · right; rw [← h]; simp

variable (Θ) in
@[expose] def pairGraph : SimpleGraph (Pair Θ) where
  Adj u v := u ≠ v ∧ ∃ p, p ∈ u.1 ∧ p ∈ v.1
  symm := ⟨fun _ _ ⟨h, p, hu, hv⟩ => ⟨fun e => h e.symm, p, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem pairGraph_adj {u v : Pair Θ} :
    (pairGraph Θ).Adj u v ↔ u ≠ v ∧ ∃ p, p ∈ u.1 ∧ p ∈ v.1 := Iff.rfl

instance : GraphAction G (pairGraph Θ) where
  adj_smul g u v := by
    rw [pairGraph_adj, pairGraph_adj]
    refine and_congr (not_congr (smul_left_cancel_iff g)) ⟨?_, ?_⟩
    · rintro ⟨p, hu, hv⟩
      exact ⟨g⁻¹ • p, (mem_smul_iff g u p).mp hu, (mem_smul_iff g v p).mp hv⟩
    · rintro ⟨p, hu, hv⟩
      exact ⟨g • p, (mem_smul_iff g u _).mpr (by simpa using hu),
        (mem_smul_iff g v _).mpr (by simpa using hv)⟩

theorem pairGraph_adj_pair {p q r : Θ} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (pairGraph Θ).Adj (pair p q hpq) (pair p r hpr) := by
  refine ⟨?_, p, by simp, by simp⟩
  intro h
  rcases pair_eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
  · exact hqr h
  · exact hpr h

theorem pairGraph_disjoint_of_dist {u v : Pair Θ} (h : (pairGraph Θ).dist u v = 2) :
    ∀ p, p ∈ u.1 → p ∉ v.1 := by
  intro p hpu hpv
  by_cases huv : u = v
  · subst huv; simp at h
  · have : (pairGraph Θ).Adj u v := ⟨huv, p, hpu, hpv⟩
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr this] at h
    exact absurd h (by norm_num)

theorem pairGraph_dist_le (u v : Pair Θ) : (pairGraph Θ).dist u v ≤ 2 := by
  by_cases huv : u = v
  · subst huv; simp
  by_cases hc : ∃ p, p ∈ u.1 ∧ p ∈ v.1
  · rw [SimpleGraph.dist_eq_one_iff_adj.mpr (pairGraph_adj.mpr ⟨huv, hc⟩)]; norm_num
  simp only [not_exists, not_and] at hc
  obtain ⟨p, q, hpq, rfl⟩ := u.exists_eq
  obtain ⟨r, s, hrs, rfl⟩ := v.exists_eq
  have hpr : p ≠ r := fun e => hc p (by simp) (by simp [e])
  have hqr : q ≠ r := fun e => hc q (by simp) (by simp [e])
  have hps : p ≠ s := fun e => hc p (by simp) (by simp [e])
  have h1 : (pairGraph Θ).Adj (pair p q hpq) (pair p r hpr) := pairGraph_adj_pair hpq hpr hqr
  have h2 : (pairGraph Θ).Adj (pair p r hpr) (pair r s hrs) := by
    rw [pair_comm p r]
    exact pairGraph_adj_pair hpr.symm hrs hps
  have := SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 .nil))
  simpa using this

theorem pairGraph_common_connected {u w : Pair Θ} (h : (pairGraph Θ).dist u w = 2) :
    ((pairGraph Θ).induce {v | (pairGraph Θ).Adj u v ∧ (pairGraph Θ).Adj w v}).Connected := by
  have hdis := pairGraph_disjoint_of_dist h
  obtain ⟨a, b, hab, rfl⟩ := u.exists_eq
  obtain ⟨c, d, hcd, rfl⟩ := w.exists_eq
  have hac : a ≠ c := fun e => hdis a (by simp) (by simp [e])
  have had : a ≠ d := fun e => hdis a (by simp) (by simp [e])
  have hbc : b ≠ c := fun e => hdis b (by simp) (by simp [e])
  have hbd : b ≠ d := fun e => hdis b (by simp) (by simp [e])
  set S : Set (Pair Θ) :=
    {v | (pairGraph Θ).Adj (pair a b hab) v ∧ (pairGraph Θ).Adj (pair c d hcd) v}
  have hmem : ∀ {x y : Θ} (hx : x = a ∨ x = b) (hy : y = c ∨ y = d) (hxy : x ≠ y),
      pair x y hxy ∈ S := by
    intro x y hx hy hxy
    refine ⟨⟨?_, x, by rcases hx with rfl | rfl <;> simp, by simp⟩,
      ⟨?_, y, by rcases hy with rfl | rfl <;> simp, by simp⟩⟩
    · intro e
      have : y ∈ (pair a b hab).1 := by rw [e]; simp
      rcases hy with rfl | rfl
      · exact hdis _ this (by simp)
      · exact hdis _ this (by simp)
    · intro e
      have : x ∈ (pair c d hcd).1 := by rw [e]; simp
      rcases hx with rfl | rfl
      · exact hdis _ (by simp) this
      · exact hdis _ (by simp) this
  have hform : ∀ v ∈ S, ∃ (x y : Θ) (hx : x = a ∨ x = b) (hy : y = c ∨ y = d) (hxy : x ≠ y),
      v = pair x y hxy := by
    rintro v ⟨⟨hne₁, x, hxu, hxv⟩, ⟨hne₂, y, hyw, hyv⟩⟩
    have hxy : x ≠ y := fun e => hdis x hxu (e ▸ hyw)
    obtain ⟨y', hxy', rfl⟩ := v.exists_eq_of_mem hxv
    have hyy' : y = y' := by
      rcases Sym2.mem_iff.mp hyv with e | e
      · exact absurd e.symm hxy
      · exact e
    subst hyy'
    exact ⟨x, y, Sym2.mem_iff.mp hxu, Sym2.mem_iff.mp hyw, hxy, rfl⟩
  have hadj : ∀ {v v' : Pair Θ} (hv : v ∈ S) (hv' : v' ∈ S), (pairGraph Θ).Adj v v' →
      ((pairGraph Θ).induce S).Reachable ⟨v, hv⟩ ⟨v', hv'⟩ := fun hv hv' h =>
    SimpleGraph.Adj.reachable (by simpa using h)
  set v₀ : S := ⟨pair a c hac, hmem (Or.inl rfl) (Or.inl rfl) hac⟩
  have hreach : ∀ v : S, ((pairGraph Θ).induce S).Reachable v₀ v := by
    rintro ⟨v, hv⟩
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := hform v hv
    have r_ad : ((pairGraph Θ).induce S).Reachable v₀
        ⟨pair a d had, hmem (Or.inl rfl) (Or.inr rfl) had⟩ :=
      hadj _ _ (pairGraph_adj_pair hac had hcd)
    have r_bc : ((pairGraph Θ).induce S).Reachable v₀
        ⟨pair b c hbc, hmem (Or.inr rfl) (Or.inl rfl) hbc⟩ := by
      refine hadj _ _ ?_
      rw [pair_comm a c, pair_comm b c]
      exact pairGraph_adj_pair hac.symm hbc.symm hab
    have r_bd : ((pairGraph Θ).induce S).Reachable v₀
        ⟨pair b d hbd, hmem (Or.inr rfl) (Or.inr rfl) hbd⟩ := by
      refine r_ad.trans (hadj _ _ ?_)
      rw [pair_comm a d, pair_comm b d]
      exact pairGraph_adj_pair had.symm hbd.symm hab
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact r_ad
    · exact r_bc
    · exact r_bd
  have : Nonempty S := ⟨v₀⟩
  exact ⟨fun v v' => (hreach v).symm.trans (hreach v')⟩

theorem pairGraph_fivegon_cond (x₀ x₁ x₂ x₃ : Pair Θ) (h01 : (pairGraph Θ).Adj x₀ x₁)
    (h12 : (pairGraph Θ).Adj x₁ x₂) (h23 : (pairGraph Θ).Adj x₂ x₃)
    (d02 : (pairGraph Θ).dist x₀ x₂ = 2) (d03 : (pairGraph Θ).dist x₀ x₃ = 2)
    (d13 : (pairGraph Θ).dist x₁ x₃ = 2) :
    ∃ v, (pairGraph Θ).Adj v x₀ ∧ (pairGraph Θ).Adj v x₂ ∧ (pairGraph Θ).Adj v x₃ := by
  have n02 := pairGraph_disjoint_of_dist d02
  have n03 := pairGraph_disjoint_of_dist d03
  have n13 := pairGraph_disjoint_of_dist d13
  obtain ⟨-, a, ha0, ha1⟩ := h01
  obtain ⟨b, hab, hx0⟩ := x₀.exists_eq_of_mem ha0
  obtain ⟨-, c, hc1, hc2⟩ := h12
  have hca : c ≠ a := fun e => n02 a ha0 (e ▸ hc2)
  obtain ⟨-, d, hd2, hd3⟩ := h23
  have hdc : d ≠ c := fun e => n13 c hc1 (e ▸ hd3)
  obtain ⟨d', hcd', hx2⟩ := x₂.exists_eq_of_mem hc2
  have hdd' : d = d' := by
    rw [hx2] at hd2
    rcases Sym2.mem_iff.mp hd2 with e | e
    · exact absurd e hdc
    · exact e
  subst hdd'
  have hda : a ≠ d := fun e => n02 a ha0 (by rw [hx2, e]; simp)
  refine ⟨pair a d hda, ?_, ?_, ?_⟩
  · refine ⟨?_, a, by simp, ha0⟩
    intro e
    have : d ∈ x₀.1 := by rw [← e]; simp
    exact n02 d this (by rw [hx2]; simp)
  · refine ⟨?_, d, by simp, hd2⟩
    intro e
    have : a ∈ x₂.1 := by rw [← e]; simp
    exact n02 a ha0 this
  · refine ⟨?_, d, by simp, hd3⟩
    intro e
    have : a ∈ x₃.1 := by rw [← e]; simp
    exact n03 a ha0 this

theorem pairGraph_triangulable : Triangulable (pairGraph Θ) :=
  triangulable_of_diam_two pairGraph_dist_le (fun _ _ h => pairGraph_common_connected h)
    pairGraph_fivegon_cond

section FourTransitive

theorem exists_fourth {a b c d : Θ} (habcd : [a, b, c, d].Nodup) (p q r : Θ) :
    ∃ s ∈ ({a, b, c, d} : Set Θ), s ≠ p ∧ s ≠ q ∧ s ≠ r := by
  classical
  by_contra hcon
  push Not at hcon
  have hsub : ({a, b, c, d} : Finset Θ) ⊆ {p, q, r} := by
    intro s hs
    have hs' : s ∈ ({a, b, c, d} : Set Θ) := by simpa using hs
    by_cases h1 : s = p
    · simp [h1]
    by_cases h2 : s = q
    · simp [h2]
    simp [hcon s hs' h1 h2]
  have h4 : ({a, b, c, d} : Finset Θ).card = 4 := by
    have e : [a, b, c, d].toFinset = {a, b, c, d} := by ext; simp
    rw [← e, List.toFinset_card_of_nodup habcd]
    rfl
  have h3 := Finset.card_le_card hsub
  have : ({p, q, r} : Finset Θ).card ≤ 3 := Finset.card_le_three
  omega

theorem exists_third {a b c d : Θ} (habcd : [a, b, c, d].Nodup) (p q : Θ) :
    ∃ s ∈ ({a, b, c, d} : Set Θ), s ≠ p ∧ s ≠ q := by
  obtain ⟨s, hs, h1, h2, -⟩ := exists_fourth habcd p q q
  exact ⟨s, hs, h1, h2⟩

variable {G : Type v} [Group G] [MulAction G Θ]

theorem exists_smul_four (h4 : IsMultiplyPretransitive G Θ 4) {a b c d a' b' c' d' : Θ}
    (h : [a, b, c, d].Nodup) (h' : [a', b', c', d'].Nodup) :
    ∃ g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' ∧ g • d = d' := by
  have inj : ∀ {a b c d : Θ}, [a, b, c, d].Nodup → Function.Injective ![a, b, c, d] := by
    intro a b c d h i j hij
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true] at h
    obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨g, hg⟩ := h4.exists_smul_eq ⟨![a, b, c, d], inj h⟩ ⟨![a', b', c', d'], inj h'⟩
  have e : ∀ i, g • ![a, b, c, d] i = ![a', b', c', d'] i := fun i =>
    congrArg (fun f : Fin 4 ↪ Θ => f i) hg
  exact ⟨g, e 0, e 1, e 2, e 3⟩

variable (G) in
abbrev quadStab (a b c d : Θ) : Subgroup G := stabilizer G ({a, b, c, d} : Set Θ)

theorem smul_quad (g : G) (a b c d : Θ) :
    g • ({a, b, c, d} : Set Θ) = {g • a, g • b, g • c, g • d} := by
  simp [Set.smul_set_insert, Set.smul_set_singleton]

theorem mem_quadStab {g : G} {a b c d : Θ}
    (h : ({g • a, g • b, g • c, g • d} : Set Θ) = {a, b, c, d}) : g ∈ quadStab G a b c d := by
  rw [mem_stabilizer_iff, smul_quad, h]

theorem exists_mem_quadStab (h4 : IsMultiplyPretransitive G Θ 4) {a b c d a' b' c' d' : Θ}
    (h : [a, b, c, d].Nodup) (h' : [a', b', c', d'].Nodup)
    (hset : ({a', b', c', d'} : Set Θ) = {a, b, c, d}) :
    ∃ g ∈ quadStab G a b c d, g • a = a' ∧ g • b = b' ∧ g • c = c' ∧ g • d = d' := by
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_smul_four h4 h h'
  exact ⟨g, mem_quadStab (by rw [h1, h2, h3, h4, hset]), h1, h2, h3, h4⟩

end FourTransitive

section PairSystem

variable {G : Type v} [Group G] [MulAction G Θ]

theorem le_of_transitive {X : Type*} [MulAction G X] {K H : Subgroup G} {x : X} (hHK : H ≤ K)
    (hstab : K ⊓ stabilizer G x ≤ H) (htr : ∀ k ∈ K, ∃ h ∈ H, h • x = k • x) : K ≤ H := by
  intro k hk
  obtain ⟨h, hh, hx⟩ := htr k hk
  have h1 : h⁻¹ * k ∈ K ⊓ stabilizer G x := by
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hHK hh)) hk, ?_⟩
    rw [mem_stabilizer_iff, mul_smul, ← hx, inv_smul_smul]
  have := H.mul_mem hh (hstab h1)
  simpa using this

theorem nodup_four_iff {a b c d : Θ} :
    [a, b, c, d].Nodup ↔ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true]
  tauto

theorem smul_pair_eq {g : G} {p q p' q' : Θ} (h : p ≠ q) (h' : p' ≠ q') (hp : g • p = p')
    (hq : g • q = q') : g • pair p q h = pair p' q' h' :=
  Subtype.ext (by simp [hp, hq])

variable {a b c d : Θ} (habcd : [a, b, c, d].Nodup)

include habcd in
theorem hcd_of : c ≠ d := (nodup_four_iff.mp habcd).2.2.2.2.2

include habcd in
theorem hbc_of : b ≠ c := (nodup_four_iff.mp habcd).2.2.2.1

@[expose] def xbar : Pair Θ := pair c d (hcd_of habcd)

@[expose] def ybar : Pair Θ := pair b c (hbc_of habcd)

theorem xbar_adj_ybar : (pairGraph Θ).Adj (xbar habcd) (ybar habcd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := nodup_four_iff.mp habcd
  rw [xbar, ybar, pair_comm b c]
  exact pairGraph_adj_pair hcd hbc.symm hbd.symm

variable (G) in
@[expose] noncomputable def pairSubgraph : (pairGraph Θ).Subgraph :=
  stdSubgraph (pairGraph Θ) (quadStab G a b c d) (xbar habcd) (ybar habcd) (xbar_adj_ybar habcd)

include habcd in
theorem quad_elems (h4 : IsMultiplyPretransitive G Θ 4) :
    (∃ g ∈ quadStab G a b c d, g • a = a ∧ g • b = d ∧ g • c = c ∧ g • d = b) ∧
    (∃ g ∈ quadStab G a b c d, g • a = b ∧ g • b = a ∧ g • c = c ∧ g • d = d) ∧
    (∃ g ∈ quadStab G a b c d, g • a = a ∧ g • b = b ∧ g • c = d ∧ g • d = c) ∧
    (∃ g ∈ quadStab G a b c d, g • a = c ∧ g • b = d ∧ g • c = a ∧ g • d = b) ∧
    (∃ g ∈ quadStab G a b c d, g • a = c ∧ g • b = a ∧ g • c = d ∧ g • d = b) ∧
    (∃ g ∈ quadStab G a b c d, g • a = b ∧ g • b = c ∧ g • c = d ∧ g • d = a) ∧
    (∃ g ∈ quadStab G a b c d, g • a = a ∧ g • b = d ∧ g • c = b ∧ g • d = c) ∧
    (∃ g ∈ quadStab G a b c d, g • a = a ∧ g • b = c ∧ g • c = d ∧ g • d = b) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := nodup_four_iff.mp habcd
  have hset : ∀ {a' b' c' d' : Θ}, (∀ x, x = a' ∨ x = b' ∨ x = c' ∨ x = d' ↔
      x = a ∨ x = b ∨ x = c ∨ x = d) → ({a', b', c', d'} : Set Θ) = {a, b, c, d} := by
    intro a' b' c' d' h
    ext x
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    refine exists_mem_quadStab h4 habcd (nodup_four_iff.mpr ?_) (hset fun x => by tauto) <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | assumption | exact Ne.symm ‹_›

theorem pairSystem_isUniquenessSystem (h4 : IsMultiplyPretransitive G Θ 4) :
    IsUniquenessSystem (pairGraph Θ) (quadStab G a b c d) (pairSubgraph G habcd) (xbar habcd)
      (ybar habcd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := nodup_four_iff.mp habcd
  obtain ⟨⟨t, ht, ta, tb, tc, td⟩, ⟨σ₁, hσ₁, σ₁a, σ₁b, σ₁c, σ₁d⟩,
    ⟨σ₂, hσ₂, σ₂a, σ₂b, σ₂c, σ₂d⟩, ⟨s, hs, sa, sb, sc, sd⟩, -, -, -, -⟩ := quad_elems habcd h4
  have htx : t • xbar habcd = ybar habcd := by
    rw [xbar, ybar, pair_comm b c]; exact smul_pair_eq _ _ tc td
  have hty : t • ybar habcd = xbar habcd := by
    rw [xbar, ybar, pair_comm c d]; exact smul_pair_eq _ _ tb tc
  have key1 : ∀ z : Pair Θ, ∃ h ∈ stabilizer G (xbar habcd) ⊔ quadStab G a b c d,
      h • xbar habcd = z := by
    intro z
    obtain ⟨p, q, hpq, rfl⟩ := z.exists_eq
    wlog hcase : (p = c ∨ p = d) ∨ ¬ (q = c ∨ q = d) generalizing p q
    · push Not at hcase
      obtain ⟨h, hh, hhz⟩ := this q p hpq.symm (Or.inl hcase.2)
      exact ⟨h, hh, by rw [hhz, pair_comm]⟩
    by_cases hp : p = c ∨ p = d
    · by_cases hq : q = c ∨ q = d
      ·
        refine ⟨1, one_mem _, ?_⟩
        rw [one_smul, xbar, pair_eq_iff]
        rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp_all
      ·
        obtain ⟨p', hp'pair, hpp'⟩ : ∃ p', (p = c ∧ p' = d ∨ p = d ∧ p' = c) ∧ p ≠ p' := by
          rcases hp with rfl | rfl
          · exact ⟨d, Or.inl ⟨rfl, rfl⟩, hcd⟩
          · exact ⟨c, Or.inr ⟨rfl, rfl⟩, hcd.symm⟩
        push Not at hq
        have hqp' : q ≠ p' := by rcases hp'pair with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp_all
        obtain ⟨r, -, hrq, hrp, hrp'⟩ := exists_fourth habcd q p p'
        obtain ⟨g, ga, gb, gc, gd⟩ := exists_smul_four (G := G) h4 habcd
          (a' := r) (b' := q) (c' := p) (d' := p')
          (nodup_four_iff.mpr ⟨hrq, hrp, hrp', hpq.symm, hqp', hpp'⟩)
        have hgx : g ∈ stabilizer G (xbar habcd) := by
          rw [mem_stabilizer_iff, xbar]
          rcases hp'pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact smul_pair_eq _ _ (gc.trans h1) (gd.trans h2)
          · rw [smul_pair_eq _ hcd.symm (gc.trans h1) (gd.trans h2), pair_comm]
        refine ⟨g * t, Subgroup.mul_mem _ (le_sup_left (b := quadStab G a b c d) hgx)
          (le_sup_right (a := stabilizer G (xbar habcd)) ht), ?_⟩
        rw [mul_smul, htx, ybar, pair_comm p q]
        exact smul_pair_eq _ _ gb gc
    ·
      have hq : ¬ (q = c ∨ q = d) := hcase.resolve_left hp
      push Not at hp hq
      obtain ⟨g, ga, gb, gc, gd⟩ := exists_smul_four (G := G) h4 habcd
        (a' := p) (b' := q) (c' := c) (d' := d)
        (nodup_four_iff.mpr ⟨hpq, hp.1, hp.2, hq.1, hq.2, hcd⟩)
      have hgx : g ∈ stabilizer G (xbar habcd) := by
        rw [mem_stabilizer_iff, xbar]; exact smul_pair_eq _ _ gc gd
      refine ⟨g * s, Subgroup.mul_mem _ (le_sup_left (b := quadStab G a b c d) hgx)
        (le_sup_right (a := stabilizer G (xbar habcd)) hs), ?_⟩
      have hsx : s • xbar habcd = pair a b hab := by
        rw [xbar]; exact smul_pair_eq _ _ sc sd
      rw [mul_smul, hsx]
      exact smul_pair_eq _ _ ga gb
  refine ⟨inferInstance, ?_, ?_, ⟨t, ht, htx, hty⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro w
    obtain ⟨h, -, hw⟩ := key1 w
    exact ⟨h, hw⟩
  ·
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨huv, p, hpu, hpv⟩
        obtain ⟨q, hpq, rfl⟩ := u.exists_eq_of_mem hpu
        obtain ⟨r, hpr, rfl⟩ := v.exists_eq_of_mem hpv
        have hqr : q ≠ r := fun e => huv (by subst e; rfl)
        obtain ⟨x₄, -, h4q, h4p, h4r⟩ := exists_fourth habcd q p r
        obtain ⟨g, ga, gb, gc, gd⟩ := exists_smul_four (G := G) h4 habcd
          (a' := x₄) (b' := r) (c' := p) (d' := q)
          (nodup_four_iff.mpr ⟨h4r, h4p, h4q, hpr.symm, hqr.symm, hpq⟩)
        refine ⟨g, ?_⟩
        show s(g • xbar habcd, g • ybar habcd) = s(pair p q hpq, pair p r hpr)
        rw [xbar, ybar, smul_pair_eq _ hpq gc gd, pair_comm b c, smul_pair_eq _ hpr gc gb]
      · rintro ⟨g, hg⟩
        have hadj := (GraphAction.adj_smul g _ _).mpr (xbar_adj_ybar habcd)
        rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact hadj
        · rw [← h1, ← h2]; exact hadj.symm
  ·
    exact stdSubgraph_verts_eq _ ht htx
  ·
    exact stdSubgraph_edgeSet_eq _
  ·
    rw [eq_top_iff]
    exact le_of_transitive (x := xbar habcd) le_top (inf_le_right.trans le_sup_left)
      fun k _ => key1 _
  ·
    refine le_antisymm (le_of_transitive (x := ybar habcd) (sup_le inf_le_left inf_le_right)
      le_sup_left ?_) (sup_le inf_le_left inf_le_right)
    intro k hk
    have hkx : k • xbar habcd = xbar habcd := mem_stabilizer_iff.mp hk
    have hadj : (pairGraph Θ).Adj (xbar habcd) (k • ybar habcd) := by
      rw [← hkx]; exact (GraphAction.adj_smul k _ _).mpr (xbar_adj_ybar habcd)
    obtain ⟨hne, p, hpx, hpz⟩ := hadj
    obtain ⟨q, hpq, hz⟩ := (k • ybar habcd).exists_eq_of_mem hpz
    rw [hz]
    have hpcd : p = c ∨ p = d := Sym2.mem_iff.mp hpx
    have hqcd : q ≠ c ∧ q ≠ d := by
      constructor
      · intro e
        rcases hpcd with h1 | h1
        · exact hpq (h1.trans e.symm)
        · apply hne; rw [hz, xbar, pair_eq_iff]; right; exact ⟨e.symm, h1.symm⟩
      · intro e
        rcases hpcd with h1 | h1
        · apply hne; rw [hz, xbar, pair_eq_iff]; left; exact ⟨h1.symm, e.symm⟩
        · exact hpq (h1.trans e.symm)
    have hσ₁x : σ₁ ∈ quadStab G a b c d ⊓ stabilizer G (xbar habcd) :=
      Subgroup.mem_inf.mpr ⟨hσ₁, by
        rw [mem_stabilizer_iff, xbar]; exact smul_pair_eq _ _ σ₁c σ₁d⟩
    have hσ₂x : σ₂ ∈ quadStab G a b c d ⊓ stabilizer G (xbar habcd) :=
      Subgroup.mem_inf.mpr ⟨hσ₂, by
        rw [mem_stabilizer_iff, xbar, smul_pair_eq _ hcd.symm σ₂c σ₂d, pair_comm]⟩
    set H := stabilizer G (xbar habcd) ⊓ stabilizer G (ybar habcd) ⊔
      quadStab G a b c d ⊓ stabilizer G (xbar habcd)
    have hσ₁H : σ₁ ∈ H := Subgroup.mem_sup_right hσ₁x
    have hσ₂H : σ₂ ∈ H := Subgroup.mem_sup_right hσ₂x
    have hσ₁y : σ₁ • ybar habcd = pair a c hac := by
      rw [ybar]; exact smul_pair_eq _ _ σ₁b σ₁c
    by_cases hqb : q = b
    · subst hqb
      rcases hpcd with rfl | rfl
      · exact ⟨1, one_mem _, by rw [one_smul, ybar, pair_comm]⟩
      · exact ⟨σ₂, hσ₂H, by rw [ybar, pair_comm p q]; exact smul_pair_eq _ _ σ₂b σ₂c⟩
    ·
      obtain ⟨g₀, g₀a, g₀b, g₀c, g₀d⟩ := exists_smul_four (G := G) h4 habcd
        (a' := q) (b' := b) (c' := c) (d' := d)
        (nodup_four_iff.mpr ⟨hqb, hqcd.1, hqcd.2, hbc, hbd, hcd⟩)
      have hg₀ : g₀ ∈ H := Subgroup.mem_sup_left
        (Subgroup.mem_inf.mpr ⟨by rw [mem_stabilizer_iff, xbar]; exact smul_pair_eq _ _ g₀c g₀d,
          by rw [mem_stabilizer_iff, ybar]; exact smul_pair_eq _ _ g₀b g₀c⟩)
      rcases hpcd with rfl | rfl
      · refine ⟨g₀ * σ₁, H.mul_mem hg₀ hσ₁H, ?_⟩
        rw [mul_smul, hσ₁y, pair_comm p q]
        exact smul_pair_eq _ _ g₀a g₀c
      · refine ⟨g₀ * σ₂ * σ₁, H.mul_mem (H.mul_mem hg₀ hσ₂H) hσ₁H, ?_⟩
        rw [mul_smul, mul_smul, hσ₁y, smul_pair_eq hac had σ₂a σ₂c, pair_comm p q]
        exact smul_pair_eq _ _ g₀a g₀d
  ·
    refine le_antisymm (le_of_transitive (x := xbar habcd) (sup_le inf_le_left inf_le_left)
      le_sup_left ?_) (sup_le inf_le_left inf_le_left)
    intro k hk
    set H := quadStab G a b c d ⊓ stabilizer G (xbar habcd) ⊔
      quadStab G a b c d ⊓ stabilizer G ({xbar habcd, ybar habcd} : Set (Pair Θ))
    have hσ₁H : σ₁ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hσ₁, by
      rw [mem_stabilizer_iff, xbar]; exact smul_pair_eq _ _ σ₁c σ₁d⟩)
    have hσ₂H : σ₂ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hσ₂, by
      rw [mem_stabilizer_iff, xbar, smul_pair_eq _ hcd.symm σ₂c σ₂d, pair_comm]⟩)
    have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨ht, by
      rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, htx, hty,
        Set.pair_comm]⟩)
    have e1 : t • xbar habcd = pair b c hbc := htx
    have e2 : σ₂ • pair b c hbc = pair b d hbd := smul_pair_eq _ _ σ₂b σ₂c
    have e3 : σ₁ • pair b c hbc = pair a c hac := smul_pair_eq _ _ σ₁b σ₁c
    have e4 : σ₂ • pair a c hac = pair a d had := smul_pair_eq _ _ σ₂a σ₂c
    have e5 : t • pair a d had = pair a b hab := smul_pair_eq _ _ ta td
    have six : ∀ {p q : Θ} (hpq : p ≠ q), (p = a ∨ p = b ∨ p = c ∨ p = d) →
        (q = a ∨ q = b ∨ q = c ∨ q = d) → ∃ h ∈ H, h • xbar habcd = pair p q hpq := by
      intro p q hpq hp hq
      have hcd' : ∃ h ∈ H, h • xbar habcd = pair c d hcd := ⟨1, one_mem _, by rw [one_smul]; rfl⟩
      have hbc' : ∃ h ∈ H, h • xbar habcd = pair b c hbc := ⟨t, htH, e1⟩
      have hbd' : ∃ h ∈ H, h • xbar habcd = pair b d hbd :=
        ⟨σ₂ * t, H.mul_mem hσ₂H htH, by rw [mul_smul, e1, e2]⟩
      have hac' : ∃ h ∈ H, h • xbar habcd = pair a c hac :=
        ⟨σ₁ * t, H.mul_mem hσ₁H htH, by rw [mul_smul, e1, e3]⟩
      have had' : ∃ h ∈ H, h • xbar habcd = pair a d had :=
        ⟨σ₂ * σ₁ * t, H.mul_mem (H.mul_mem hσ₂H hσ₁H) htH, by rw [mul_smul, mul_smul, e1, e3, e4]⟩
      have hab' : ∃ h ∈ H, h • xbar habcd = pair a b hab :=
        ⟨t * σ₂ * σ₁ * t, H.mul_mem (H.mul_mem (H.mul_mem htH hσ₂H) hσ₁H) htH,
          by rw [mul_smul, mul_smul, mul_smul, e1, e3, e4, e5]⟩
      have sw : ∀ {p q : Θ} {hpq : p ≠ q}, (∃ h ∈ H, h • xbar habcd = pair p q hpq) →
          ∃ h ∈ H, h • xbar habcd = pair q p hpq.symm := by
        rintro p q hpq ⟨h, hh, e⟩; exact ⟨h, hh, by rw [e, pair_comm]⟩
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hpq | assumption | exact sw ‹_›
    have hmem : ∀ x, x = a ∨ x = b ∨ x = c ∨ x = d → k • x = a ∨ k • x = b ∨ k • x = c ∨
        k • x = d := by
      intro x hx
      have := (MulAction.mem_stabilizer_set.mp hk x).mpr (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact hx)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    obtain ⟨h, hh, e⟩ := six ((MulAction.injective k).ne hcd) (hmem c (by simp)) (hmem d (by simp))
    exact ⟨h, hh, by rw [e, xbar, smul_pair]⟩

theorem pairSystem_isBase (h4 : IsMultiplyPretransitive G Θ 4) :
    IsBase G (pairGraph Θ) (pairSubgraph G habcd) := by
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := nodup_four_iff.mp habcd
  obtain ⟨-, -, ⟨σ₂, hσ₂, σ₂a, σ₂b, σ₂c, σ₂d⟩, -, ⟨g₅, hg₅, g₅a, g₅b, g₅c, g₅d⟩,
    ⟨g₆, hg₆, g₆a, g₆b, g₆c, g₆d⟩, ⟨g₇, hg₇, g₇a, g₇b, g₇c, g₇d⟩,
    ⟨g₈, hg₈, g₈a, g₈b, g₈c, g₈d⟩⟩ := quad_elems habcd h4
  set ΓI := pairSubgraph G habcd
  have hadjI : ∀ {i : G}, i ∈ quadStab G a b c d → ∀ {u v : Pair Θ},
      i • xbar habcd = u → i • ybar habcd = v → ΓI.Adj u v :=
    fun hi _ _ hu hv => ⟨_, hi, Or.inl ⟨hu, hv⟩⟩
  have hsub : ∀ {u v w : Pair Θ}, ΓI.Adj u v → ΓI.Adj v w → ΓI.Adj w u →
      IsSubCycle ΓI [u, v, w, u] := by
    intro u v w h1 h2 h3
    refine ⟨⟨⟨List.cons_ne_nil _ _, ?_⟩, rfl⟩, ?_⟩
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true,
        SimpleGraph.Subgraph.spanningCoe_adj]
      exact ⟨h1, h2, h3⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ΓI.edge_vert h1
      · exact ΓI.edge_vert h2
      · exact ΓI.edge_vert h3
      · exact ΓI.edge_vert h1
  have tri1 : IsSubCycle ΓI [pair d c hcd.symm, pair d b hbd.symm, pair d a had.symm,
      pair d c hcd.symm] := by
    refine hsub (hadjI hσ₂ ?_ ?_) (hadjI hg₅ ?_ ?_) (hadjI hg₆ ?_ ?_)
    · exact smul_pair_eq _ _ σ₂c σ₂d
    · rw [ybar, pair_comm d b]; exact smul_pair_eq _ _ σ₂b σ₂c
    · exact smul_pair_eq _ _ g₅c g₅d
    · rw [ybar, pair_comm d a]; exact smul_pair_eq _ _ g₅b g₅c
    · exact smul_pair_eq _ _ g₆c g₆d
    · rw [ybar, pair_comm d c]; exact smul_pair_eq _ _ g₆b g₆c
  have tri2 : IsSubCycle ΓI [pair c d hcd, pair c b hbc.symm, pair d b hbd.symm,
      pair c d hcd] := by
    refine hsub (hadjI (one_mem _) ?_ ?_) (hadjI hg₇ ?_ ?_) (hadjI hg₈ ?_ ?_)
    · rw [one_smul]; rfl
    · rw [one_smul, ybar, pair_comm]
    · rw [pair_comm c b]; exact smul_pair_eq _ _ g₇c g₇d
    · exact smul_pair_eq _ _ g₇b g₇c
    · exact smul_pair_eq _ _ g₈c g₈d
    · exact smul_pair_eq _ _ g₈b g₈c
  have htri : ∀ e, IsNGon (pairGraph Θ) 3 e →
      ∃ (c₀ : List (Pair Θ)) (g : G), IsSubCycle ΓI c₀ ∧ e = c₀.map (g • ·) := by
    intro e he
    obtain ⟨u, v, w, rfl, huv, hvw, hwu⟩ := he.three
    obtain ⟨hne₁, p, hpu, hpv⟩ := huv
    obtain ⟨q, hpq, rfl⟩ := u.exists_eq_of_mem hpu
    obtain ⟨r, hpr, rfl⟩ := v.exists_eq_of_mem hpv
    have hqr : q ≠ r := fun h => hne₁ (by subst h; rfl)
    by_cases hpw : p ∈ w.1
    · obtain ⟨s', hps, rfl⟩ := w.exists_eq_of_mem hpw
      have hsq : s' ≠ q := fun h => hwu.1 (by subst h; rfl)
      have hsr : s' ≠ r := fun h => hvw.1 (by subst h; rfl)
      obtain ⟨g, ga, gb, gc, gd⟩ := exists_smul_four (G := G) h4 habcd
        (a' := s') (b' := r) (c' := q) (d' := p)
        (nodup_four_iff.mpr ⟨hsr, hsq, hps.symm, hqr.symm, hpr.symm, hpq.symm⟩)
      refine ⟨_, g, tri1, ?_⟩
      simp only [List.map_cons, List.map_nil]
      rw [smul_pair_eq _ hpq gd gc, smul_pair_eq _ hpr gd gb, smul_pair_eq _ hps gd ga]
    ·
      obtain ⟨-, x₁, hx₁w, hx₁u⟩ := hwu
      obtain ⟨-, x₂, hx₂v, hx₂w⟩ := hvw
      have hqw : q ∈ w.1 := by
        rcases Sym2.mem_iff.mp hx₁u with h | h
        · exact absurd (h ▸ hx₁w) hpw
        · exact h ▸ hx₁w
      have hrw : r ∈ w.1 := by
        rcases Sym2.mem_iff.mp hx₂v with h | h
        · exact absurd (h ▸ hx₂w) hpw
        · exact h ▸ hx₂w
      obtain ⟨r', hqr', hw⟩ := w.exists_eq_of_mem hqw
      have hrr' : r = r' := by
        rw [hw] at hrw
        rcases Sym2.mem_iff.mp hrw with h | h
        · exact absurd h.symm hqr
        · exact h
      subst hrr'
      subst hw
      obtain ⟨x₄, -, h4r, h4p, h4q⟩ := exists_fourth habcd r p q
      obtain ⟨g, ga, gb, gc, gd⟩ := exists_smul_four (G := G) h4 habcd
        (a' := x₄) (b' := r) (c' := p) (d' := q)
        (nodup_four_iff.mpr ⟨h4r, h4p, h4q, hpr.symm, hqr.symm, hpq⟩)
      refine ⟨_, g, tri2, ?_⟩
      simp only [List.map_cons, List.map_nil]
      rw [smul_pair_eq _ hpq gc gd, smul_pair_eq _ hpr gc gb, smul_pair_eq _ hqr gd gb]
  intro cyc hcyc
  refine (pairGraph_triangulable cyc hcyc).of_rotRev ?_
  intro e he w hw hl
  have h3 : IsNGon (pairGraph Θ) 3 e := rotRev_ngon_eq_subset 3 he
  have hmem := htri e h3
  simpa using Moves.cycDel_mem (Γ := pairGraph Θ)
    (C := {d | ∃ (c₀ : List (Pair Θ)) (g : G), IsSubCycle ΓI c₀ ∧ d = c₀.map (g • ·)})
    [] [] e hmem hw hl

end PairSystem

end CFSG.Quasithin.Asc94
