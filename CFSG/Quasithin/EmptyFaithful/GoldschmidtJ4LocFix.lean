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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.Quasithin.J4Loc

variable {G : Type*} [Group G]

theorem exists_fixed_mod [Finite G] {T B M : Subgroup G} (hT : IsPGroup 2 T) (hBM : B ≤ M)
    (hMT : M ≤ T) (hne : B ≠ M) (hBn : ∀ t ∈ T, ∀ x ∈ B, t * x * t⁻¹ ∈ B)
    (hMn : ∀ t ∈ T, ∀ x ∈ M, t * x * t⁻¹ ∈ M) :
    ∃ m ∈ M, m ∉ B ∧ ∀ t ∈ T, t * m * t⁻¹ * m⁻¹ ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B' : Subgroup T := B.subgroupOf T
  let M' : Subgroup T := M.subgroupOf T
  have hB'n : B'.Normal :=
    ⟨fun x hx t => by
      show ((t * x * t⁻¹ : T) : G) ∈ B
      have h1 : ((t * x * t⁻¹ : T) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl
      rw [h1]
      exact hBn t t.2 x hx⟩
  have hM'n : M'.Normal :=
    ⟨fun x hx t => by
      show ((t * x * t⁻¹ : T) : G) ∈ M
      have h1 : ((t * x * t⁻¹ : T) : G) = (t : G) * (x : G) * (t : G)⁻¹ := rfl
      rw [h1]
      exact hMn t t.2 x hx⟩
  have hQ : IsPGroup 2 (T ⧸ B') := hT.to_quotient B'
  have hnil : Group.IsNilpotent (T ⧸ B') := hQ.isNilpotent
  let π : T →* T ⧸ B' := QuotientGroup.mk' B'
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective B'
  let X : Subgroup (T ⧸ B') := M'.map π
  have hXn : X.Normal := Subgroup.Normal.map hM'n π hπ
  obtain ⟨m0, hm0M, hm0B⟩ : ∃ m0 ∈ M, m0 ∉ B := by
    by_contra hcon
    refine hne (le_antisymm hBM fun x hx => ?_)
    by_contra hxB
    exact hcon ⟨x, hx, hxB⟩
  have hX : X ≠ ⊥ := by
    intro hXb
    have h1 : π ⟨m0, hMT hm0M⟩ ∈ X := Subgroup.mem_map_of_mem π (by
      show m0 ∈ M
      exact hm0M)
    rw [hXb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hm0B h1
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hX
  obtain ⟨q, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc
  have hqX : (q : T ⧸ B') ∈ X := q.2.1
  have hqZ : (q : T ⧸ B') ∈ Subgroup.center (T ⧸ B') := q.2.2
  obtain ⟨m1, hm1M, hm1q⟩ := (Subgroup.mem_map).1 hqX
  refine ⟨(m1 : G), hm1M, ?_, ?_⟩
  · intro hmB
    apply hq1
    have : (q : T ⧸ B') = 1 := by
      rw [← hm1q, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmB
    exact Subtype.ext this
  · intro t ht
    have hz := Subgroup.mem_center_iff.1 hqZ (π ⟨t, ht⟩)
    rw [← hm1q] at hz
    have h2 : π (⟨t, ht⟩ * m1 * ⟨t, ht⟩⁻¹ * m1⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hz]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2

end CFSG.Quasithin.J4Loc
