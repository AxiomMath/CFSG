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

public section

namespace CFSG.SignalizerFunctor.Helpers

theorem integral_coprime_multiples (first second : ℕ) (coprime : Nat.Coprime first second) (value : ℂ)
    (first_integral : IsIntegral ℤ ((first : ℂ) * value))
    (second_integral : IsIntegral ℤ ((second : ℂ) * value)) : IsIntegral ℤ value := by
  have bezout := Nat.gcd_eq_gcd_ab first second
  rw [coprime] at bezout
  have complex_bezout : (1 : ℂ) = (first : ℂ) * (first.gcdA second : ℂ) +
      (second : ℂ) * (first.gcdB second : ℂ) := by exact_mod_cast bezout
  have first_term := first_integral.zsmul (first.gcdA second)
  have second_term := second_integral.zsmul (first.gcdB second)
  have integral := first_term.add second_term
  have equal : (first.gcdA second : ℤ) • ((first : ℂ) * value) +
      (first.gcdB second : ℤ) • ((second : ℂ) * value) = value := by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    calc
      _ = ((first : ℂ) * (first.gcdA second : ℂ) + (second : ℂ) * (first.gcdB second : ℂ)) * value := by ring
      _ = value := by rw [← complex_bezout, one_mul]
  rwa [equal] at integral

theorem integral_coprime_quotient (numerator : ℂ) (degree classSize : ℕ) (degree_positive : 0 < degree)
    (coprime : Nat.Coprime degree classSize) (numerator_integral : IsIntegral ℤ numerator)
    (central_integral : IsIntegral ℤ ((classSize : ℂ) * numerator / degree)) :
    IsIntegral ℤ (numerator / degree) := by
  have degree_ne : (degree : ℂ) ≠ 0 := by exact_mod_cast degree_positive.ne'
  apply integral_coprime_multiples degree classSize coprime (numerator / degree)
  · have equal : (degree : ℂ) * (numerator / degree) = numerator := by field_simp
    rwa [equal]
  · simpa only [mul_div_assoc] using central_integral

end CFSG.SignalizerFunctor.Helpers
