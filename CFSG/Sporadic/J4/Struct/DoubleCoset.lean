module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.J4.Struct

open Finset

variable {G : Type*} [Group G]

@[expose] def dcSet (K : Subgroup G) (w : G) : Set G := {g | ∃ k ∈ K, ∃ k' ∈ K, k * w * k' = g}

theorem mem_dcSet_self (K : Subgroup G) (w : G) : w ∈ dcSet K w :=
  ⟨1, K.one_mem, 1, K.one_mem, by simp⟩

theorem dcSet_one (K : Subgroup G) : dcSet K 1 = (K : Set G) := by
  ext g
  constructor
  · rintro ⟨k, hk, k', hk', rfl⟩
    simpa using K.mul_mem hk hk'
  · intro hg
    exact ⟨g, hg, 1, K.one_mem, by simp⟩

theorem dcSet_subset_of_mem {K : Subgroup G} {u v g : G} (hu : g ∈ dcSet K u)
    (hv : g ∈ dcSet K v) : dcSet K u ⊆ dcSet K v := by
  obtain ⟨k1, hk1, k2, hk2, rfl⟩ := hu
  obtain ⟨k3, hk3, k4, hk4, he⟩ := hv
  rintro x ⟨k5, hk5, k6, hk6, rfl⟩
  refine ⟨k5 * k1⁻¹ * k3, K.mul_mem (K.mul_mem hk5 (K.inv_mem hk1)) hk3,
    k4 * k2⁻¹ * k6, K.mul_mem (K.mul_mem hk4 (K.inv_mem hk2)) hk6, ?_⟩
  have hu' : u = k1⁻¹ * (k3 * v * k4) * k2⁻¹ := by
    rw [he]
    group
  rw [hu']
  group

theorem dcSet_eq_of_mem {K : Subgroup G} {u v g : G} (hu : g ∈ dcSet K u) (hv : g ∈ dcSet K v) :
    dcSet K u = dcSet K v :=
  Set.Subset.antisymm (dcSet_subset_of_mem hu hv) (dcSet_subset_of_mem hv hu)

theorem mem_of_dcSet {K L : Subgroup G} (hKL : K ≤ L) {w g : G} (hg : g ∈ dcSet K w)
    (hgL : g ∈ L) : w ∈ L := by
  obtain ⟨k, hk, k', hk', rfl⟩ := hg
  have := L.mul_mem (L.mul_mem (L.inv_mem (hKL hk)) hgL) (L.inv_mem (hKL hk'))
  simpa [mul_assoc] using this

theorem dcSet_subset {K L : Subgroup G} (hKL : K ≤ L) {w : G} (hw : w ∈ L) :
    dcSet K w ⊆ (L : Set G) := by
  rintro x ⟨k1, hk1, k2, hk2, rfl⟩
  exact L.mul_mem (L.mul_mem (hKL hk1) hw) (hKL hk2)

section Cover

variable [Fintype G] (K : Subgroup G) {m : ℕ} (w : Fin m → G) (n : Fin m → ℕ)

@[expose] def wO (o : Option (Fin m)) : G := o.elim 1 w

@[expose] def nO (o : Option (Fin m)) : ℕ := o.elim 1 n

open Classical in
@[expose] noncomputable def dcF (o : Option (Fin m)) : Finset G := (dcSet K (wO w o)).toFinset

theorem mem_dcF {o : Option (Fin m)} {g : G} : g ∈ dcF K w o ↔ g ∈ dcSet K (wO w o) := by
  classical
  simp [dcF]

theorem card_dcF (o : Option (Fin m)) : (dcF K w o).card = (dcSet K (wO w o)).ncard := by
  classical
  rw [dcF, Set.ncard_eq_toFinset_card']

theorem card_dcF_none : (dcF K w none).card = Nat.card K := by
  rw [card_dcF, wO, Option.elim_none, dcSet_one, ← Nat.card_coe_set_eq]
  rfl

theorem dcF_eq_of_mem {o o' : Option (Fin m)} {g : G} (h : g ∈ dcF K w o) (h' : g ∈ dcF K w o') :
    dcF K w o = dcF K w o' := by
  classical
  have e := dcSet_eq_of_mem ((mem_dcF K w).1 h) ((mem_dcF K w).1 h')
  ext x
  rw [mem_dcF, mem_dcF, e]

theorem card_dcF_pos (o : Option (Fin m)) : 0 < (dcF K w o).card :=
  Finset.card_pos.2 ⟨_, (mem_dcF K w).2 (mem_dcSet_self K _)⟩

variable {K w n}

theorem dcF_exact (hcov : ∀ g : G, g ∈ K ∨ ∃ i, g ∈ dcSet K (w i))
    (hsz : ∀ i, (dcSet K (w i)).ncard ≤ Nat.card K * n i)
    (hG : Nat.card K * (1 + ∑ i, n i) ≤ Nat.card G) :
    (∀ o, (dcF K w o).card = Nat.card K * nO n o) ∧
      (Set.univ : Set (Option (Fin m))).PairwiseDisjoint (dcF K w) ∧
      Nat.card G = Nat.card K * (1 + ∑ i, n i) := by
  classical
  have hcovF : (Finset.univ : Finset G) = Finset.univ.biUnion (dcF K w) := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_biUnion, true_and, true_iff]
    rcases hcov g with h | ⟨i, h⟩
    · exact ⟨none, (mem_dcF K w).2 (by rw [wO, Option.elim_none, dcSet_one]; exact h)⟩
    · exact ⟨some i, (mem_dcF K w).2 h⟩
  have hle : ∀ o, (dcF K w o).card ≤ Nat.card K * nO n o := by
    rintro (_ | i)
    · rw [card_dcF_none, nO, Option.elim_none, mul_one]
    · rw [card_dcF]
      exact hsz i
  have hsumO : ∑ o, Nat.card K * nO n o = Nat.card K * (1 + ∑ i, n i) := by
    rw [Fintype.sum_option, ← Finset.mul_sum, nO, Option.elim_none, mul_add, mul_one]
    rfl
  have hcardG : Nat.card G = (Finset.univ : Finset G).card := by
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  have hchain : Nat.card G ≤ ∑ o, (dcF K w o).card := by
    rw [hcardG, hcovF]
    exact Finset.card_biUnion_le
  have hsum2 : ∑ o, (dcF K w o).card ≤ ∑ o, Nat.card K * nO n o := Finset.sum_le_sum fun o _ => hle o
  have heq : ∑ o, (dcF K w o).card = ∑ o, Nat.card K * nO n o := by omega
  have hexact : ∀ o, (dcF K w o).card = Nat.card K * nO n o := by
    intro o
    exact (Finset.sum_eq_sum_iff_of_le fun o _ => hle o).1 heq o (Finset.mem_univ o)
  refine ⟨hexact, ?_, by omega⟩
  intro o _ o' _ hne
  by_contra hd
  obtain ⟨g, hg, hg'⟩ := Finset.not_disjoint_iff.1 hd
  have e := dcF_eq_of_mem K w hg hg'
  have hsub : (Finset.univ : Finset G) ⊆ (Finset.univ.erase o').biUnion (dcF K w) := by
    intro x _
    have hx : x ∈ Finset.univ.biUnion (dcF K w) := hcovF ▸ Finset.mem_univ x
    obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 hx
    by_cases hpo : p = o'
    · subst hpo
      exact Finset.mem_biUnion.2 ⟨o, Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩, e ▸ hp⟩
    · exact Finset.mem_biUnion.2 ⟨p, Finset.mem_erase.2 ⟨hpo, Finset.mem_univ _⟩, hp⟩
  have h1 : Nat.card G ≤ ∑ p ∈ Finset.univ.erase o', (dcF K w p).card := by
    rw [hcardG]
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 := Finset.sum_erase_add (s := Finset.univ) (f := fun p => (dcF K w p).card)
    (Finset.mem_univ o')
  have h3 := card_dcF_pos K w o'
  omega

theorem isCoatom_of_dcSet (hcov : ∀ g : G, g ∈ K ∨ ∃ i, g ∈ dcSet K (w i))
    (hsz : ∀ i, (dcSet K (w i)).ncard ≤ Nat.card K * n i)
    (hG : Nat.card K * (1 + ∑ i, n i) ≤ Nat.card G)
    (hprim : ∀ S : Finset (Fin m), (1 + ∑ i ∈ S, n i) ∣ (1 + ∑ i, n i) → S = ∅ ∨ S = Finset.univ)
    (hm : 0 < ∑ i, n i) : IsCoatom K := by
  classical
  obtain ⟨hexact, hdisj, hcardG⟩ := dcF_exact hcov hsz hG
  have hK0 : 0 < Nat.card K := Nat.card_pos
  refine ⟨fun hK => ?_, fun L hKL => ?_⟩
  · have : Nat.card K = Nat.card G := by rw [hK, Subgroup.card_top]
    rw [hcardG] at this
    have : Nat.card K * 1 < Nat.card K * (1 + ∑ i, n i) := Nat.mul_lt_mul_of_pos_left (by omega) hK0
    omega
  set S : Finset (Fin m) := Finset.univ.filter fun i => w i ∈ L with hS
  set T : Finset (Option (Fin m)) := insert none (S.map Function.Embedding.some) with hT
  have hL : (L : Set G).toFinset = T.biUnion (dcF K w) := by
    ext g
    simp only [Set.mem_toFinset, SetLike.mem_coe, Finset.mem_biUnion]
    constructor
    · intro hg
      rcases hcov g with h | ⟨i, h⟩
      · exact ⟨none, Finset.mem_insert_self _ _,
          (mem_dcF K w).2 (by rw [wO, Option.elim_none, dcSet_one]; exact h)⟩
      · refine ⟨some i, Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ ?_), (mem_dcF K w).2 h⟩
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_of_dcSet hKL.le h hg⟩
    · rintro ⟨o, ho, hg⟩
      have hg' := (mem_dcF K w).1 hg
      rcases Finset.mem_insert.1 ho with rfl | ho
      · rw [wO, Option.elim_none, dcSet_one] at hg'
        exact hKL.le hg'
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 ho
        exact dcSet_subset hKL.le (Finset.mem_filter.1 hi).2 hg'
  have hcardL : Nat.card L = Nat.card K * (1 + ∑ i ∈ S, n i) := by
    have h1 : Nat.card L = ((L : Set G).toFinset).card :=
      Nat.card_eq_card_toFinset (L : Set G)
    rw [h1, hL, Finset.card_biUnion (fun o _ o' _ h => hdisj (Set.mem_univ o) (Set.mem_univ o') h),
      Finset.sum_insert (by simp), Finset.sum_map]
    simp only [hexact, nO, Option.elim_none, Option.elim_some, mul_one, Function.Embedding.some_apply]
    rw [mul_add, mul_one, Finset.mul_sum]
  have hdvd : Nat.card L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
  rw [hcardL, hcardG] at hdvd
  rcases hprim S (Nat.dvd_of_mul_dvd_mul_left hK0 hdvd) with h | h
  · exfalso
    apply hKL.2
    intro g hg
    rcases hcov g with h' | ⟨i, h'⟩
    · exact h'
    · have : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_of_dcSet hKL.le h' hg⟩
      rw [h] at this
      simp at this
  · rw [eq_top_iff]
    intro g _
    rcases hcov g with h' | ⟨i, h'⟩
    · exact hKL.le h'
    · have hi : i ∈ S := h ▸ Finset.mem_univ i
      exact dcSet_subset hKL.le (Finset.mem_filter.1 hi).2 h'

end Cover

end CFSG.Sporadic.J4.Struct
