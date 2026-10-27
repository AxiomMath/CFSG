module

public import CFSG.Permutation.FiveTransitive.Degree20SevenFiniteChecks
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

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem sylow_long_prime_card_eq_prime
    (P : Type) [Group P] [Fintype P]
    (h : ℕ) (hPcard : Nat.card P = 1860480 * h)
    (hdiv : h ∣ 186624000)
    {p : ℕ} (hpCases : p = 17 ∨ p = 19)
    (S : Sylow p P) :
    Nat.card S = p := by
  classical
  rcases hpCases with rfl | rfl
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    have hnot : ¬17 ∣ h := by
      intro hdvd
      have : 17 ∣ 186624000 := hdvd.trans hdiv
      norm_num at this
    have hh : h ≠ 0 := by
      intro hz
      subst h
      exact hnot (dvd_zero 17)
    have hfactorization :
        (1860480 * h).factorization 17 = 1 := by
      rw [show 1860480 = 17 * 109440 by norm_num,
        Nat.mul_assoc,
        Nat.factorization_mul (by norm_num)
          (Nat.mul_ne_zero (by norm_num) hh),
        Finsupp.add_apply,
        (show Nat.Prime 17 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) hh,
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd hnot]
      norm_num
    rw [S.card_eq_multiplicity, hPcard,
      hfactorization]
    norm_num
  · letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
    have hnot : ¬19 ∣ h := by
      intro hdvd
      have : 19 ∣ 186624000 := hdvd.trans hdiv
      norm_num at this
    have hh : h ≠ 0 := by
      intro hz
      subst h
      exact hnot (dvd_zero 19)
    have hfactorization :
        (1860480 * h).factorization 19 = 1 := by
      rw [show 1860480 = 19 * 97920 by norm_num,
        Nat.mul_assoc,
        Nat.factorization_mul (by norm_num)
          (Nat.mul_ne_zero (by norm_num) hh),
        Finsupp.add_apply,
        (show Nat.Prime 19 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_mul (by norm_num) hh,
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd hnot]
      norm_num
    rw [S.card_eq_multiplicity, hPcard,
      hfactorization]
    norm_num

end FiveTransitive.Degree20

end CFSG
