module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.Monster.B.Generic

open MulAction
open scoped Pointwise

theorem exists_adj_adj_of_ediam_le_two {V : Type*} {X : SimpleGraph V} (hdiam : X.ediam ≤ 2)
    (htri : ∀ u v, X.Adj u v → ∃ w, X.Adj u w ∧ X.Adj v w) {u v : V} (huv : u ≠ v) :
    ∃ w, X.Adj u w ∧ X.Adj v w := by
  by_cases h : X.Adj u v
  · exact htri u v h
  · have h2 : ¬ 2 < X.edist u v := not_lt.mpr (X.edist_le_ediam.trans hdiam)
    rw [SimpleGraph.two_lt_edist_iff] at h2
    obtain ⟨w, hw⟩ : (X.commonNeighbors u v).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun he => h2 ⟨huv, h, he⟩
    exact ⟨w, (X.mem_commonNeighbors).mp hw⟩

theorem neighborSet_smul_of_adj_smul_iff {V K : Type*} [Group K] [MulAction K V]
    {X : SimpleGraph V} (hK : ∀ (k : K) (u v : V), X.Adj (k • u) (k • v) ↔ X.Adj u v) (k : K)
    (x : V) : X.neighborSet (k • x) = k • X.neighborSet x := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, SimpleGraph.mem_neighborSet,
    SimpleGraph.mem_neighborSet, ← hK k x (k⁻¹ • y), smul_inv_smul]

theorem isBlock_preimage_neighborSet {V K : Type*} [Group K] [MulAction K V] (X : SimpleGraph V)
    (x : V) {B : Set V} (hB : IsBlock K B) :
    IsBlock (stabilizer (stabilizer K x) (X.neighborSet x))
      (Subtype.val ⁻¹' B : Set (X.neighborSet x)) :=
  hB.preimage (φ := fun g : stabilizer (stabilizer K x) (X.neighborSet x) =>
      ((g : stabilizer K x) : K))
    { toFun := Subtype.val, map_smul' := fun _ _ => rfl }

theorem locally_primitive_diameter_two_action {V : Type*} (X : SimpleGraph V)
    (hdiam : X.ediam ≤ 2)
    (htri : ∀ u v, X.Adj u v → ∃ w, X.Adj u w ∧ X.Adj v w)
    {K : Type*} [Group K] [MulAction K V]
    (hK : ∀ (k : K) (u v : V), X.Adj (k • u) (k • v) ↔ X.Adj u v) [IsPretransitive K V]
    (hloc : ∀ x : V, IsPreprimitive (stabilizer (stabilizer K x) (X.neighborSet x))
      (X.neighborSet x)) :
    IsPreprimitive K V := by
  refine { isTrivialBlock_of_isBlock := fun {B} hB => ?_ }
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact Or.inl Set.subsingleton_of_subsingleton
  have hcn : ∀ {u v : V}, u ≠ v → ∃ w, X.Adj u w ∧ X.Adj v w := fun huv =>
    exists_adj_adj_of_ediam_le_two hdiam htri huv
  have htrace : ∀ (x : V) (g : K),
      (Subtype.val ⁻¹' (g • B) : Set (X.neighborSet x)).Subsingleton ∨
        (Subtype.val ⁻¹' (g • B) : Set (X.neighborSet x)) = Set.univ := fun x g =>
    (hloc x).isTrivialBlock_of_isBlock (isBlock_preimage_neighborSet X x (hB.translate g))
  rcases B.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · exact Or.inl Set.subsingleton_empty
  by_cases hcase : ∃ x : V, ∃ g : K, X.neighborSet x ⊆ g • B
  · right
    obtain ⟨x₀, g₀, h₀⟩ := hcase
    have hall : ∀ w : V, ∃ g : K, X.neighborSet w ⊆ g • B := by
      intro w
      obtain ⟨k, rfl⟩ := exists_smul_eq K x₀ w
      refine ⟨k * g₀, ?_⟩
      rw [neighborSet_smul_of_adj_smul_iff hK, mul_smul]
      exact Set.smul_set_mono h₀
    have hself : ∀ (w : V) (g : K), X.neighborSet w ⊆ g • B → w ∈ g • B := by
      intro w g hg
      obtain ⟨w', hw'⟩ := exists_ne w
      obtain ⟨y, hwy, -⟩ := hcn hw'.symm
      obtain ⟨z, hwz, hyz⟩ := htri w y hwy
      obtain ⟨g', hg'⟩ := hall y
      have heq : g • B = g' • B := hB.smul_eq_smul_of_nonempty ⟨z, hg hwz, hg' hyz⟩
      rw [heq]
      exact hg' hwy.symm
    have hclosed : ∀ t v : V, t ∈ g₀ • B → X.Adj t v → v ∈ g₀ • B := by
      intro t v ht htv
      obtain ⟨g, hg⟩ := hall t
      have heq : g₀ • B = g • B := hB.smul_eq_smul_of_nonempty ⟨t, ht, hself t g hg⟩
      rw [heq]
      exact hg htv
    have ht : g₀ • b ∈ g₀ • B := Set.smul_mem_smul_set hb
    have huniv : g₀ • B = Set.univ := by
      refine Set.eq_univ_of_forall fun v => ?_
      by_cases hv : g₀ • b = v
      · exact hv ▸ ht
      · obtain ⟨z, hz1, hz2⟩ := hcn hv
        exact hclosed z v (hclosed _ z ht hz1) hz2.symm
    rw [← inv_smul_smul g₀ B, huniv, Set.smul_set_univ]
  · left
    intro u hu v hv
    by_contra huv
    obtain ⟨w, hwu, hwv⟩ := hcn huv
    rcases htrace w 1 with h | h
    · have hu' : (⟨u, hwu.symm⟩ : X.neighborSet w) ∈
          (Subtype.val ⁻¹' ((1 : K) • B) : Set (X.neighborSet w)) := by simpa using hu
      have hv' : (⟨v, hwv.symm⟩ : X.neighborSet w) ∈
          (Subtype.val ⁻¹' ((1 : K) • B) : Set (X.neighborSet w)) := by simpa using hv
      exact huv (congrArg Subtype.val (h hu' hv'))
    · refine hcase ⟨w, 1, fun y hy => ?_⟩
      have hy' : (⟨y, hy⟩ : X.neighborSet w) ∈
          (Subtype.val ⁻¹' ((1 : K) • B) : Set (X.neighborSet w)) := by
        rw [h]
        exact Set.mem_univ _
      exact hy'

end CFSG.Monster.B.Generic
