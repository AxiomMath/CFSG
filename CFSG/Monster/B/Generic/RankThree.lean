module

public import CFSG.Fischer.Classification.SRG.Conference
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B.Generic

open MulAction Finset
open scoped Pointwise

noncomputable def suborbitGraph (H Ω : Type*) [Group H] [MulAction H Ω] (k : ℕ) :
    SimpleGraph Ω :=
  SimpleGraph.fromRel fun α β => Nat.card (orbit (stabilizer H α) β) = k

section Suborbit

variable {H Ω : Type*} [Group H] [MulAction H Ω]

theorem card_orbit_stabilizer_eq_relIndex (α β : Ω) :
    Nat.card (orbit (stabilizer H α) β) = (stabilizer H β).relIndex (stabilizer H α) := by
  rw [Subgroup.relIndex, stabilizer_subgroupOf, index_stabilizer, Nat.card_coe_set_eq]

theorem card_orbit_stabilizer_self (α : Ω) : Nat.card (orbit (stabilizer H α) α) = 1 := by
  rw [card_orbit_stabilizer_eq_relIndex, Subgroup.relIndex_self]

theorem card_orbit_stabilizer_smul (h : H) (α β : Ω) :
    Nat.card (orbit (stabilizer H (h • α)) (h • β)) = Nat.card (orbit (stabilizer H α) β) := by
  rw [card_orbit_stabilizer_eq_relIndex, card_orbit_stabilizer_eq_relIndex,
    stabilizer_smul_eq_stabilizer_map_conj, stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj h).injective]

theorem card_orbit_stabilizer_comm [Finite Ω] [IsPretransitive H Ω] (α β : Ω) :
    Nat.card (orbit (stabilizer H α) β) = Nat.card (orbit (stabilizer H β) α) := by
  have : Nonempty Ω := ⟨α⟩
  rw [card_orbit_stabilizer_eq_relIndex, card_orbit_stabilizer_eq_relIndex]
  have h1 := Subgroup.relIndex_mul_index
    (inf_le_left (a := stabilizer H α) (b := stabilizer H β))
  have h2 := Subgroup.relIndex_mul_index
    (inf_le_right (a := stabilizer H α) (b := stabilizer H β))
  rw [Subgroup.inf_relIndex_left, index_stabilizer_of_transitive] at h1
  rw [Subgroup.inf_relIndex_right, index_stabilizer_of_transitive] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem suborbitGraph_adj {k : ℕ} {α β : Ω} : (suborbitGraph H Ω k).Adj α β ↔
    α ≠ β ∧ (Nat.card (orbit (stabilizer H α) β) = k ∨
      Nat.card (orbit (stabilizer H β) α) = k) :=
  SimpleGraph.fromRel_adj _ _ _

theorem suborbitGraph_adj_iff [Finite Ω] [IsPretransitive H Ω] {k : ℕ} (hk : k ≠ 1)
    {α β : Ω} :
    (suborbitGraph H Ω k).Adj α β ↔ Nat.card (orbit (stabilizer H α) β) = k := by
  rw [suborbitGraph_adj, card_orbit_stabilizer_comm β α, or_self]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  rintro rfl
  rw [card_orbit_stabilizer_self] at h
  exact hk h.symm

theorem suborbitGraph_adj_smul (k : ℕ) (h : H) (α β : Ω) :
    (suborbitGraph H Ω k).Adj (h • α) (h • β) ↔ (suborbitGraph H Ω k).Adj α β := by
  simp only [suborbitGraph_adj, card_orbit_stabilizer_smul, ne_eq, smul_left_cancel_iff]

end Suborbit

theorem dvd_card_filter_card_orbit_eq {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    (k : ℕ) : k ∣ (univ.filter fun x : X => Nat.card (orbit G x) = k).card := by
  classical
  rw [card_eq_sum_card_image (fun x => orbit G x), sum_const_nat (m := k)]
  · exact Dvd.intro_left _ rfl
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
    have hxk : Nat.card (orbit G x) = k := (mem_filter.mp hx).2
    have : ((univ.filter fun x : X => Nat.card (orbit G x) = k).filter
        fun a => orbit G a = orbit G x) = (orbit G x).toFinset := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset]
      constructor
      · rintro ⟨-, h⟩
        exact orbit_eq_iff.mp h
      · intro h
        have h' := orbit_eq_iff.mpr h
        exact ⟨h' ▸ hxk, h'⟩
    rw [this, Set.toFinset_card, ← Nat.card_eq_fintype_card, hxk]

theorem mem_orbit_of_card_filter_card_orbit_eq {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] {k : ℕ} (hk : (univ.filter fun x : X => Nat.card (orbit G x) = k).card = k)
    {x y : X} (hx : Nat.card (orbit G x) = k) (hy : Nat.card (orbit G y) = k) :
    y ∈ orbit G x := by
  classical
  have hsub : (orbit G x).toFinset ⊆ univ.filter fun z : X => Nat.card (orbit G z) = k := by
    intro z hz
    rw [Set.mem_toFinset] at hz
    rw [mem_filter, orbit_eq_iff.mpr hz]
    exact ⟨mem_univ _, hx⟩
  have hcard : (orbit G x).toFinset.card = k := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, hx]
  have heq := eq_of_subset_of_card_le hsub (by rw [hk, hcard])
  have hy' : y ∈ univ.filter fun z : X => Nat.card (orbit G z) = k :=
    mem_filter.mpr ⟨mem_univ _, hy⟩
  rw [← heq, Set.mem_toFinset] at hy'
  exact hy'

theorem card_commonNeighbors_smul {V K : Type*} [Fintype V] [Group K] [MulAction K V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hK : ∀ (k : K) (u v : V), G.Adj (k • u) (k • v) ↔ G.Adj u v) (k : K) (u v : V) :
    Fintype.card (G.commonNeighbors (k • u) (k • v)) = Fintype.card (G.commonNeighbors u v) :=
  (Fintype.card_congr (Equiv.subtypeEquiv (MulAction.toPerm k) fun x => by
    simp only [SimpleGraph.mem_commonNeighbors, MulAction.toPerm_apply, hK])).symm

theorem isBlock_setOf_eq_or_adj {V K : Type*} [Group K] [MulAction K V] {G : SimpleGraph V}
    (hK : ∀ (k : K) (u v : V), G.Adj (k • u) (k • v) ↔ G.Adj u v)
    (htr : ∀ u v w, G.Adj u v → G.Adj v w → u ≠ w → G.Adj u w) (a : V) :
    IsBlock K {x | a = x ∨ G.Adj a x} := by
  have hsymm : ∀ x y : V, (x = y ∨ G.Adj x y) → (y = x ∨ G.Adj y x) := by
    rintro x y (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm
  have htrans : ∀ x y z : V, (x = y ∨ G.Adj x y) → (y = z ∨ G.Adj y z) →
      (x = z ∨ G.Adj x z) := by
    rintro x y z (rfl | hxy) (rfl | hyz)
    · exact Or.inl rfl
    · exact Or.inr hyz
    · exact Or.inr hxy
    · by_cases hxz : x = z
      · exact Or.inl hxz
      · exact Or.inr (htr x y z hxy hyz hxz)
  have hsmul : ∀ g : K, g • {x | a = x ∨ G.Adj a x} = {x | g • a = x ∨ G.Adj (g • a) x} := by
    intro g
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      ← hK g a (g⁻¹ • x), smul_inv_smul, eq_inv_smul_iff]
  rw [isBlock_iff_smul_eq_of_nonempty]
  rintro g ⟨z, hz1, hz2⟩
  rw [hsmul] at hz1 ⊢
  have hga : a = g • a ∨ G.Adj a (g • a) := htrans _ _ _ hz2 (hsymm _ _ hz1)
  ext x
  exact ⟨fun h => htrans _ _ _ hga h, fun h => htrans _ _ _ (hsymm _ _ hga) h⟩

theorem not_isSquare_of_mul_self_lt {n D : ℤ} (hn : 0 ≤ n) (h1 : n * n < D)
    (h2 : D < (n + 1) * (n + 1)) : ¬ IsSquare D := by
  rintro ⟨r, rfl⟩
  have habs : |r| * |r| = r * r := abs_mul_abs_self r
  have h0 := abs_nonneg r
  rcases le_or_gt |r| n with h | h
  · nlinarith
  · have h' : n + 1 ≤ |r| := h
    nlinarith

section Degree2300

variable {H Ω : Type*} [Group H] [MulAction H Ω] [Fintype Ω]

private theorem card_filter_891_and_1408 (hcard : Fintype.card Ω = 2300)
    (hsub : ∀ α β : Ω, β ≠ α → Nat.card (orbit (stabilizer H α) β) = 891 ∨
      Nat.card (orbit (stabilizer H α) β) = 1408) (α : Ω) :
    (univ.filter fun β : Ω => Nat.card (orbit (stabilizer H α) β) = 891).card = 891 ∧
    (univ.filter fun β : Ω => Nat.card (orbit (stabilizer H α) β) = 1408).card = 1408 := by
  classical
  have h1 := dvd_card_filter_card_orbit_eq (G := stabilizer H α) (X := Ω) 891
  have h2 := dvd_card_filter_card_orbit_eq (G := stabilizer H α) (X := Ω) 1408
  have hsplit : (univ.filter fun β : Ω => Nat.card (orbit (stabilizer H α) β) = 891).card +
      (univ.filter fun β : Ω => ¬ Nat.card (orbit (stabilizer H α) β) = 891).card =
      (univ : Finset Ω).card := card_filter_add_card_filter_not _
  have hneg : (univ.filter fun β : Ω => ¬ Nat.card (orbit (stabilizer H α) β) = 891) =
      insert α (univ.filter fun β : Ω => Nat.card (orbit (stabilizer H α) β) = 1408) := by
    ext β
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    by_cases hβ : β = α
    · subst hβ
      rw [card_orbit_stabilizer_self]
      simp
    · have := hsub α β hβ
      simp only [hβ, false_or]
      omega
  have hα : α ∉ univ.filter fun β : Ω => Nat.card (orbit (stabilizer H α) β) = 1408 := by
    rw [mem_filter, card_orbit_stabilizer_self]
    simp
  rw [hneg, card_insert_of_notMem hα, card_univ, hcard] at hsplit
  omega

private theorem exists_smul_eq_smul_pair (hcard : Fintype.card Ω = 2300)
    (hsub : ∀ α β : Ω, β ≠ α → Nat.card (orbit (stabilizer H α) β) = 891 ∨
      Nat.card (orbit (stabilizer H α) β) = 1408)
    [IsPretransitive H Ω] {k : ℕ} (hk : k = 891 ∨ k = 1408) {α β α' β' : Ω}
    (h1 : Nat.card (orbit (stabilizer H α) β) = k)
    (h2 : Nat.card (orbit (stabilizer H α') β') = k) :
    ∃ h : H, h • α = α' ∧ h • β = β' := by
  obtain ⟨g, rfl⟩ := exists_smul_eq H α α'
  have hlev := card_filter_891_and_1408 hcard hsub (g • α)
  have h3 : Nat.card (orbit (stabilizer H (g • α)) (g • β)) = k := by
    rw [card_orbit_stabilizer_smul]
    exact h1
  have hk' : (univ.filter fun x : Ω =>
      Nat.card (orbit (stabilizer H (g • α)) x) = k).card = k := by
    rcases hk with rfl | rfl
    exacts [hlev.1, hlev.2]
  obtain ⟨s, hs⟩ := mem_orbit_of_card_filter_card_orbit_eq hk' h3 h2
  refine ⟨(s : H) * g, ?_, ?_⟩
  · rw [mul_smul]
    exact mem_stabilizer_iff.mp s.2
  · rw [mul_smul]
    exact hs

private theorem params_eq {l m : ℕ} (h : 891 * (891 - l - 1) = (2300 - 891 - 1) * m)
    (hm : m ≠ 0) (hsq : IsSquare (((l : ℤ) - m) ^ 2 + 4 * (((891 : ℕ) : ℤ) - m))) :
    l = 378 ∧ m = 324 := by
  obtain ⟨t, rfl⟩ : 81 ∣ m := by omega
  obtain ⟨rfl, ht⟩ : l = 890 - 128 * t ∧ t ≤ 6 := by omega
  interval_cases t
  · omega
  · exact absurd hsq (not_isSquare_of_mul_self_lt (n := 683) (by norm_num) (by norm_num)
      (by norm_num))
  · exact absurd hsq (not_isSquare_of_mul_self_lt (n := 475) (by norm_num) (by norm_num)
      (by norm_num))
  · exact absurd hsq (not_isSquare_of_mul_self_lt (n := 267) (by norm_num) (by norm_num)
      (by norm_num))
  · omega
  · exact absurd hsq (not_isSquare_of_mul_self_lt (n := 161) (by norm_num) (by norm_num)
      (by norm_num))
  · exact absurd hsq (not_isSquare_of_mul_self_lt (n := 366) (by norm_num) (by norm_num)
      (by norm_num))

private theorem connected_diam_isSRGWith (hcard : Fintype.card Ω = 2300)
    (hsub : ∀ α β : Ω, β ≠ α → Nat.card (orbit (stabilizer H α) β) = 891 ∨
      Nat.card (orbit (stabilizer H α) β) = 1408)
    [IsPreprimitive H Ω] {G : SimpleGraph Ω} [DecidableRel G.Adj]
    (hadj : ∀ α β : Ω, G.Adj α β ↔ Nat.card (orbit (stabilizer H α) β) = 891) :
    G.Connected ∧ G.diam = 2 ∧ G.IsSRGWith 2300 891 378 324 := by
  have hK : ∀ (h : H) (α β : Ω), G.Adj (h • α) (h • β) ↔ G.Adj α β := fun h α β => by
    rw [hadj, hadj, card_orbit_stabilizer_smul]
  have hpos : 0 < Fintype.card Ω := by omega
  obtain ⟨α₀⟩ := Fintype.card_pos_iff.mp hpos
  have hlev := card_filter_891_and_1408 hcard hsub α₀
  obtain ⟨β₀, hβ₀⟩ : (univ.filter fun β : Ω =>
      Nat.card (orbit (stabilizer H α₀) β) = 891).Nonempty := by
    rw [← card_pos, hlev.1]
    norm_num
  obtain ⟨γ₀, hγ₀⟩ : (univ.filter fun β : Ω =>
      Nat.card (orbit (stabilizer H α₀) β) = 1408).Nonempty := by
    rw [← card_pos, hlev.2]
    norm_num
  replace hβ₀ := (mem_filter.mp hβ₀).2
  replace hγ₀ := (mem_filter.mp hγ₀).2
  have hαβ : α₀ ≠ β₀ := by
    rintro rfl
    rw [card_orbit_stabilizer_self] at hβ₀
    omega
  have hαγ : α₀ ≠ γ₀ := by
    rintro rfl
    rw [card_orbit_stabilizer_self] at hγ₀
    omega
  have hnadj : ¬ G.Adj α₀ γ₀ := by
    rw [hadj]
    omega
  have hsrg : G.IsSRGWith 2300 891 (Fintype.card (G.commonNeighbors α₀ β₀))
      (Fintype.card (G.commonNeighbors α₀ γ₀)) := by
    refine ⟨hcard, fun v => ?_, fun v w hvw => ?_, ?_⟩
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
        filter_congr fun x _ => hadj v x]
      exact (card_filter_891_and_1408 hcard hsub v).1
    · obtain ⟨h, rfl, rfl⟩ :=
        exists_smul_eq_smul_pair hcard hsub (Or.inl rfl) hβ₀ ((hadj v w).mp hvw)
      exact card_commonNeighbors_smul G hK h α₀ β₀
    · intro v w hvw hn
      have hvw' : Nat.card (orbit (stabilizer H v) w) = 1408 := by
        rcases hsub v w hvw.symm with h | h
        · exact absurd ((hadj v w).mpr h) hn
        · exact h
      obtain ⟨h, rfl, rfl⟩ := exists_smul_eq_smul_pair hcard hsub (Or.inr rfl) hγ₀ hvw'
      exact card_commonNeighbors_smul G hK h α₀ γ₀
  have hμ : Fintype.card (G.commonNeighbors α₀ γ₀) ≠ 0 := by
    intro hμ0
    have htr : ∀ u v w, G.Adj u v → G.Adj v w → u ≠ w → G.Adj u w := by
      intro u v w huv hvw huw
      by_contra hn
      have h0 := hsrg.of_not_adj huw hn
      rw [hμ0, Fintype.card_eq_zero_iff] at h0
      exact h0.false ⟨v, (G.mem_commonNeighbors).mpr ⟨huv, hvw.symm⟩⟩
    have hB := isBlock_setOf_eq_or_adj hK htr α₀
    rcases IsPreprimitive.isTrivialBlock_of_isBlock hB with hs | hu
    · exact hαβ (hs (Or.inl rfl) (Or.inr ((hadj α₀ β₀).mpr hβ₀)))
    · have hγ : γ₀ ∈ {x | α₀ = x ∨ G.Adj α₀ x} := by
        rw [hu]
        exact Set.mem_univ _
      rcases hγ with h | h
      exacts [hαγ h, hnadj h]
  have hconf := not_not.mp fun hns =>
    absurd (hsrg.conference_of_not_isSquare (by norm_num) hns).1 (by decide)
  obtain ⟨hl, hm⟩ := params_eq (SimpleGraph.IsSRGWith.param_eq G hsrg (by norm_num)) hμ hconf
  rw [hl, hm] at hsrg
  have hne : G ≠ ⊤ := by
    intro htop
    apply hnadj
    rw [htop]
    exact (SimpleGraph.top_adj α₀ γ₀).mpr hαγ
  have : Nontrivial Ω := ⟨⟨α₀, γ₀, hαγ⟩⟩
  have hdiam := hsrg.ediam_eq_two hne (by norm_num)
  refine ⟨SimpleGraph.connected_iff_ediam_ne_top.mpr (by simp [hdiam]), ?_, hsrg⟩
  simp [SimpleGraph.diam, hdiam]

end Degree2300

theorem rank_three_2300_graph_parameters {H Ω : Type*} [Group H] [MulAction H Ω] [Fintype Ω]
    [IsPreprimitive H Ω] (hcard : Fintype.card Ω = 2300)
    (hsub : ∀ α β : Ω, β ≠ α → Nat.card (orbit (stabilizer H α) β) = 891 ∨
      Nat.card (orbit (stabilizer H α) β) = 1408)
    [DecidableRel (suborbitGraph H Ω 891).Adj] :
    (∀ α β : Ω, Nat.card (orbit (stabilizer H α) β) = 891 →
      Nat.card (orbit (stabilizer H β) α) = 891) ∧
    (∀ α β : Ω, (suborbitGraph H Ω 891).Adj α β ↔
      Nat.card (orbit (stabilizer H α) β) = 891) ∧
    (suborbitGraph H Ω 891).Connected ∧ (suborbitGraph H Ω 891).diam = 2 ∧
    (suborbitGraph H Ω 891).IsSRGWith 2300 891 378 324 := by
  have hadj : ∀ α β : Ω, (suborbitGraph H Ω 891).Adj α β ↔
      Nat.card (orbit (stabilizer H α) β) = 891 := fun _ _ => suborbitGraph_adj_iff (by norm_num)
  exact ⟨fun α β h => (card_orbit_stabilizer_comm β α).trans h, hadj,
    connected_diam_isSRGWith hcard hsub hadj⟩

end CFSG.Monster.B.Generic
