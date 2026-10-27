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

open scoped commutatorElement

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem central_commutator_mul_left
    (central : ∀ first second : GroupType, ⁅first, second⁆ ∈ Subgroup.center GroupType)
    (first second third : GroupType) :
    ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have commutes := Subgroup.mem_center_iff.mp (central second third) first
  have conjugate : first * ⁅second, third⁆ * first⁻¹ = ⁅second, third⁆ := by
    rw [commutes, mul_assoc, mul_inv_cancel, mul_one]
  rw [conjugate]
  exact Subgroup.mem_center_iff.mp (central first third) ⁅second, third⁆

theorem central_commutator_mul_right
    (central : ∀ first second : GroupType, ⁅first, second⁆ ∈ Subgroup.center GroupType)
    (first second third : GroupType) :
    ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have commutes := Subgroup.mem_center_iff.mp (central first third) second
  have conjugate : second * ⁅first, third⁆ * second⁻¹ = ⁅first, third⁆ := by
    rw [commutes, mul_assoc, mul_inv_cancel, mul_one]
  calc
    _ = ⁅first, second⁆ * (second * ⁅first, third⁆ * second⁻¹) := by group
    _ = _ := by rw [conjugate]

theorem central_commutator_conjugate_invariant (element first second : GroupType)
    (central : ⁅first, second⁆ ∈ Subgroup.center GroupType) :
    element * ⁅first, second⁆ * element⁻¹ = ⁅first, second⁆ := by
  rw [Subgroup.mem_center_iff.mp central element, mul_assoc, mul_inv_cancel, mul_one]

theorem class_two_quadratic_pair_commutator_square
    (central : ∀ first second : GroupType, ⁅first, second⁆ ∈ Subgroup.center GroupType)
    (firstAutomorphism secondAutomorphism : GroupType ≃* GroupType)
    (first_preserves : ∀ first second : GroupType,
      firstAutomorphism ⁅first, second⁆ = ⁅first, second⁆)
    (second_preserves : ∀ first second : GroupType,
      secondAutomorphism ⁅first, second⁆ = ⁅first, second⁆)
    (automorphisms_commute : ∀ element : GroupType,
      firstAutomorphism (secondAutomorphism element) = secondAutomorphism (firstAutomorphism element))
    (element : GroupType) :
    let firstDifference := element⁻¹ * firstAutomorphism element
    let secondDifference := element⁻¹ * secondAutomorphism element
    let firstMixed := secondDifference⁻¹ * firstAutomorphism secondDifference
    let secondMixed := firstDifference⁻¹ * secondAutomorphism firstDifference
    firstAutomorphism firstMixed = firstMixed → secondAutomorphism firstMixed = firstMixed →
    firstAutomorphism secondMixed = secondMixed → secondAutomorphism secondMixed = secondMixed →
    ⁅firstDifference, secondDifference⁆ ^ 2 = 1 := by
  let firstDifference := element⁻¹ * firstAutomorphism element
  let secondDifference := element⁻¹ * secondAutomorphism element
  let firstMixed := secondDifference⁻¹ * firstAutomorphism secondDifference
  let secondMixed := firstDifference⁻¹ * secondAutomorphism firstDifference
  change firstAutomorphism firstMixed = firstMixed → secondAutomorphism firstMixed = firstMixed →
    firstAutomorphism secondMixed = secondMixed → secondAutomorphism secondMixed = secondMixed →
    ⁅firstDifference, secondDifference⁆ ^ 2 = 1
  intro first_fixed_firstMixed second_fixed_firstMixed first_fixed_secondMixed second_fixed_secondMixed
  have first_image : firstAutomorphism element = element * firstDifference := by
    dsimp only [firstDifference]
    group
  have second_image : secondAutomorphism element = element * secondDifference := by
    dsimp only [secondDifference]
    group
  have first_mixed_image : firstAutomorphism secondDifference = secondDifference * firstMixed := by
    dsimp only [firstMixed]
    group
  have second_mixed_image : secondAutomorphism firstDifference = firstDifference * secondMixed := by
    dsimp only [secondMixed]
    group
  have first_pair_invariant : ∀ first second : GroupType,
      ⁅firstAutomorphism first, firstAutomorphism second⁆ = ⁅first, second⁆ := by
    intro first second
    exact (map_commutatorElement firstAutomorphism first second).symm.trans (first_preserves first second)
  have second_pair_invariant : ∀ first second : GroupType,
      ⁅secondAutomorphism first, secondAutomorphism second⁆ = ⁅first, second⁆ := by
    intro first second
    exact (map_commutatorElement secondAutomorphism first second).symm.trans (second_preserves first second)
  have first_annihilates : ⁅firstDifference, firstMixed⁆ = 1 := by
    have invariant := first_pair_invariant element firstMixed
    rw [first_image, first_fixed_firstMixed, central_commutator_mul_left central] at invariant
    exact mul_left_cancel (by simpa only [mul_one] using invariant)
  have second_annihilates : ⁅secondDifference, secondMixed⁆ = 1 := by
    have invariant := second_pair_invariant element secondMixed
    rw [second_image, second_fixed_secondMixed, central_commutator_mul_left central] at invariant
    exact mul_left_cancel (by simpa only [mul_one] using invariant)
  have first_identity : ⁅firstDifference, secondDifference⁆ * ⁅element, firstMixed⁆ = 1 := by
    have invariant := first_pair_invariant element secondDifference
    rw [first_image, first_mixed_image,
      central_commutator_mul_right central (element * firstDifference) secondDifference firstMixed,
      central_commutator_mul_left central element firstDifference secondDifference,
      central_commutator_mul_left central element firstDifference firstMixed,
      first_annihilates, mul_one] at invariant
    rw [mul_assoc] at invariant
    exact mul_left_cancel (by simpa only [mul_one] using invariant)
  have second_identity : ⁅secondDifference, firstDifference⁆ * ⁅element, secondMixed⁆ = 1 := by
    have invariant := second_pair_invariant element firstDifference
    rw [second_image, second_mixed_image,
      central_commutator_mul_right central (element * secondDifference) firstDifference secondMixed,
      central_commutator_mul_left central element secondDifference firstDifference,
      central_commutator_mul_left central element secondDifference secondMixed,
      second_annihilates, mul_one] at invariant
    rw [mul_assoc] at invariant
    exact mul_left_cancel (by simpa only [mul_one] using invariant)
  have mixed_equation : firstDifference * secondDifference * firstMixed =
      secondDifference * firstDifference * secondMixed := by
    have equation : firstAutomorphism (element * secondDifference) =
        secondAutomorphism (element * firstDifference) := by
      simpa only [← first_image, ← second_image] using automorphisms_commute element
    have first_evaluation : firstAutomorphism (element * secondDifference) =
        element * (firstDifference * secondDifference * firstMixed) := by
      calc
        _ = firstAutomorphism element * firstAutomorphism secondDifference := map_mul _ _ _
        _ = (element * firstDifference) * (secondDifference * firstMixed) :=
          congrArg₂ (· * ·) first_image first_mixed_image
        _ = _ := by group
    have second_evaluation : secondAutomorphism (element * firstDifference) =
        element * (secondDifference * firstDifference * secondMixed) := by
      calc
        _ = secondAutomorphism element * secondAutomorphism firstDifference := map_mul _ _ _
        _ = (element * secondDifference) * (firstDifference * secondMixed) :=
          congrArg₂ (· * ·) second_image second_mixed_image
        _ = _ := by group
    rw [first_evaluation, second_evaluation] at equation
    exact mul_left_cancel equation
  have second_mixed_formula : secondMixed = ⁅firstDifference, secondDifference⁆ * firstMixed := by
    have conjugation := central_commutator_conjugate_invariant (secondDifference * firstDifference)⁻¹
      firstDifference secondDifference (central firstDifference secondDifference)
    calc
      secondMixed = (secondDifference * firstDifference)⁻¹ *
          (firstDifference * secondDifference * firstMixed) := by rw [mixed_equation]; group
      _ = ((secondDifference * firstDifference)⁻¹ * ⁅firstDifference, secondDifference⁆ *
          ((secondDifference * firstDifference)⁻¹)⁻¹) * firstMixed := by
            rw [commutatorElement_def]
            group
      _ = ⁅firstDifference, secondDifference⁆ * firstMixed := by rw [conjugation]
  have mixed_pair_equal : ⁅element, secondMixed⁆ = ⁅element, firstMixed⁆ := by
    rw [second_mixed_formula, central_commutator_mul_right central,
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (central firstDifference secondDifference) element), one_mul]
  rw [mixed_pair_equal] at second_identity
  have same_commutator : ⁅firstDifference, secondDifference⁆ = ⁅secondDifference, firstDifference⁆ :=
    mul_right_cancel (first_identity.trans second_identity.symm)
  calc
    ⁅firstDifference, secondDifference⁆ ^ 2 =
        ⁅firstDifference, secondDifference⁆ * ⁅secondDifference, firstDifference⁆ := by
          rw [pow_two, same_commutator]
    _ = 1 := by rw [← commutatorElement_inv, inv_mul_cancel]

end CFSG.SignalizerFunctor.Helpers
