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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section CoreAlg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem core_alg (B : V →ₗ[K] V →ₗ[K] K) (hB : ∀ x y, B x y = B y x) (F : V →+ V)
    (e f : Fin 3 → V) (hef : ∀ i j, B (e i) (f j) = if i = j then 1 else 0)
    (hee : ∀ i j, B (e i) (e j) = 0) (hff : ∀ i j, B (f i) (f j) = 0)
    (hcomm : ∀ i j, i ≠ j → ∀ x, F (B x (f j) • e i - B x (e i) • f j) =
      B (F x) (f j) • e i - B (F x) (e i) • f j) :
    ∃ a b : K, (∀ i, F (e i) = a • e i) ∧ (∀ i, F (f i) = b • f i) := by
  have hef1 : ∀ i, B (e i) (f i) = 1 := fun i => by simpa using hef i i
  have hef0 : ∀ i j, i ≠ j → B (e i) (f j) = 0 := fun i j h => by simpa [h] using hef i j
  have hfe1 : ∀ i, B (f i) (e i) = 1 := fun i => by rw [hB, hef1]
  have hfe0 : ∀ i j, i ≠ j → B (f j) (e i) = 0 := fun i j h => by rw [hB, hef0 i j h]
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := hef1 i
    rw [h] at this
    simp at this
  have hnf : ∀ i, f i ≠ 0 := fun i h => by
    have := hef1 i
    rw [hB, h] at this
    simp at this
  have E1 : ∀ i j, i ≠ j → F (e i) = B (F (e j)) (f j) • e i - B (F (e j)) (e i) • f j := by
    intro i j hij
    have := hcomm i j hij (e j)
    rwa [hef1 j, hee j i, zero_smul, sub_zero, one_smul] at this
  have E2 : ∀ i j, i ≠ j → F (f j) = B (F (f i)) (e i) • f j - B (F (f i)) (f j) • e i := by
    intro i j hij
    have := hcomm i j hij (f i)
    rw [hff i j, hfe1 i, zero_smul, zero_sub, one_smul, map_neg] at this
    rw [neg_eq_iff_eq_neg, neg_sub] at this
    exact this
  have Ee : ∀ i j j', i ≠ j → i ≠ j' → j ≠ j' → F (e i) = B (F (e j)) (f j) • e i := by
    intro i j j' hij hij' hjj'
    have h1 := E1 i j hij
    have h2 := E1 i j' hij'
    have h4 := congrArg (fun z => B z (e j)) (h1.symm.trans h2)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hee,
      hfe1, hfe0 j j' hjj', mul_zero, zero_sub, mul_one, neg_inj] at h4
    rw [h1, h4, zero_smul, sub_zero]
  have Ef : ∀ j i i', j ≠ i → j ≠ i' → i ≠ i' → F (f j) = B (F (f i)) (e i) • f j := by
    intro j i i' hji hji' hii'
    have h1 := E2 i j (Ne.symm hji)
    have h2 := E2 i' j (Ne.symm hji')
    have h4 := congrArg (fun z => B z (f i)) (h1.symm.trans h2)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hff,
      hef1, hef0 i' i (Ne.symm hii'), mul_zero, zero_sub, mul_one, neg_inj] at h4
    rw [h1, h4, zero_smul, sub_zero]
  have three : ∀ i : Fin 3, ∃ j j' : Fin 3, i ≠ j ∧ i ≠ j' ∧ j ≠ j' := by decide
  have hα : ∀ i, ∃ α : K, F (e i) = α • e i := fun i => by
    obtain ⟨j, j', hij, hij', hjj'⟩ := three i
    exact ⟨_, Ee i j j' hij hij' hjj'⟩
  have hβ : ∀ i, ∃ β : K, F (f i) = β • f i := fun i => by
    obtain ⟨j, j', hij, hij', hjj'⟩ := three i
    exact ⟨_, Ef i j j' hij hij' hjj'⟩
  choose α hα using hα
  choose β hβ using hβ
  have hαeq : ∀ i j, α i = α j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h1 := E1 i j hij
      rw [hα j, hα i] at h1
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hef1, hee, mul_one,
        mul_zero, zero_smul, sub_zero] at h1
      exact smul_left_injective K (hne i) h1
  have hβeq : ∀ i j, β i = β j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h1 := E2 i j hij
      rw [hβ j, hβ i] at h1
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hff, hfe1, mul_one,
        mul_zero, zero_smul, sub_zero] at h1
      exact (smul_left_injective K (hnf j) h1).symm
  exact ⟨α 0, β 0, fun i => by rw [hα i, hαeq i 0], fun i => by rw [hβ i, hβeq i 0]⟩

end CoreAlg

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
