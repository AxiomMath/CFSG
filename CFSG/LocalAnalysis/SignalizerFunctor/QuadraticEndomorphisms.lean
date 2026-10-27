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
public import Mathlib.RingTheory.PiTensorProduct
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

universe ringUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {RingType : Type ringUniverse} [Ring RingType]

theorem square_zero_one_add_power (nilpotent : RingType) (square_zero : nilpotent ^ 2 = 0)
    (exponent : ℕ) : (1 + nilpotent) ^ exponent = 1 + (exponent : RingType) * nilpotent := by
  have product_zero : nilpotent * nilpotent = 0 := by rwa [pow_two] at square_zero
  induction exponent with
  | zero => simp
  | succ exponent induction_hypothesis =>
    rw [pow_succ, induction_hypothesis, Nat.cast_succ]
    calc
      (1 + (exponent : RingType) * nilpotent) * (1 + nilpotent) =
          1 + ((exponent : RingType) + 1) * nilpotent + (exponent : RingType) * (nilpotent * nilpotent) := by
        noncomm_ring
      _ = 1 + ((exponent : RingType) + 1) * nilpotent := by rw [product_zero, mul_zero, add_zero]

theorem quadratic_ring_element_prime_power (prime : ℕ) [CharP RingType prime]
    (element : RingType) (quadratic : (element - 1) ^ 2 = 0) : element ^ prime = 1 := by
  have power := square_zero_one_add_power (element - 1) quadratic prime
  have one_add : 1 + (element - 1) = element := by noncomm_ring
  rw [one_add, CharP.cast_eq_zero RingType prime, zero_mul, add_zero] at power
  exact power

theorem quadratic_ring_element_conjugate (element : RingType) (quadratic : (element - 1) ^ 2 = 0)
    (conjugator : RingTypeˣ) :
    ((conjugator⁻¹ : RingTypeˣ).val * element * conjugator.val - 1) ^ 2 = 0 := by
  have difference_eq : (conjugator⁻¹ : RingTypeˣ).val * element * conjugator.val - 1 =
      (conjugator⁻¹ : RingTypeˣ).val * (element - 1) * conjugator.val := by
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
  rw [difference_eq, pow_two]
  calc
    ((conjugator⁻¹ : RingTypeˣ).val * (element - 1) * conjugator.val) *
        ((conjugator⁻¹ : RingTypeˣ).val * (element - 1) * conjugator.val) =
        (conjugator⁻¹ : RingTypeˣ).val * (element - 1) *
          (conjugator.val * (conjugator⁻¹ : RingTypeˣ).val) * (element - 1) * conjugator.val := by
      noncomm_ring
    _ = (conjugator⁻¹ : RingTypeˣ).val * ((element - 1) ^ 2) * conjugator.val := by
      rw [Units.mul_inv, mul_one, pow_two]
      noncomm_ring
    _ = 0 := by rw [quadratic, mul_zero, zero_mul]

end CFSG.SignalizerFunctor.Helpers
