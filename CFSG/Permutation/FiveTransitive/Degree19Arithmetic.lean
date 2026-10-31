module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG

namespace FiveTransitive.Degree19

abbrev SeventeenNormalizerRatio :=
  ↥(Nat.divisors 16)

abbrev NineteenNormalizerRatio :=
  ↥(Nat.divisors 18)

@[expose] def stabilizerFactorArithmeticPredicate
    (a : Fin 12)
    (b : Fin 6) : Prop :=
  let h := 2 ^ a.val * 3 ^ b.val
  (3 * h) % 5 = 1 →
    ((4 * h) % 17 = 2 ∨
      (4 * h) % 17 = 4 ∨
      (4 * h) % 17 = 8 ∨
      (4 * h) % 17 = 16) →
    ((5 * h) % 19 = 1 ∨
      (5 * h) % 19 = 2 ∨
      (5 * h) % 19 = 3 ∨
      (5 * h) % 19 = 6 ∨
      (5 * h) % 19 = 9 ∨
      (5 * h) % 19 = 18) →
    h = 2 ∨ h = 72

theorem stabilizer_factor_arithmetic :
    ∀ a : Fin 12,
      ∀ b : Fin 6,
        stabilizerFactorArithmeticPredicate a b := by
  letI (a : Fin 12)
      (b : Fin 6) :
      Decidable
        (stabilizerFactorArithmeticPredicate a b) := by
    dsimp only [stabilizerFactorArithmeticPredicate]
    infer_instance
  letI : Decidable
      (∀ a : Fin 12,
        ∀ b : Fin 6,
          stabilizerFactorArithmeticPredicate a b) :=
    Fintype.decidableForallFintype
  decide

theorem seventeen_normalizer_ratio_cases
    (r : SeventeenNormalizerRatio) (hr : 2 ≤ r.val) :
    r.val = 2 ∨ r.val = 4 ∨ r.val = 8 ∨ r.val = 16 := by
  have hrdvd : r.val ∣ 16 :=
    (Nat.mem_divisors.mp r.prop).1
  have hrle : r.val ≤ 16 :=
    Nat.le_of_dvd (by norm_num) hrdvd
  interval_cases r.val
  all_goals try norm_num at hrdvd
  all_goals try norm_num at hr
  all_goals norm_num

theorem nineteen_normalizer_ratio_cases
    (r : NineteenNormalizerRatio) :
    r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨
      r.val = 6 ∨ r.val = 9 ∨ r.val = 18 := by
  have hrdvd : r.val ∣ 18 :=
    (Nat.mem_divisors.mp r.prop).1
  have hrpos : 0 < r.val :=
    Nat.pos_of_dvd_of_pos hrdvd (by norm_num)
  have hrle : r.val ≤ 18 :=
    Nat.le_of_dvd (by norm_num) hrdvd
  interval_cases r.val
  all_goals try norm_num at hrdvd
  all_goals norm_num

theorem exists_two_three_power_of_dvd_four_hundred_ninety_seven_thousand
    {h : ℕ} (hdvd : h ∣ 497664) :
    ∃ a ≤ 11, ∃ b ≤ 5, h = 2 ^ a * 3 ^ b := by
  have hfactor :
      Nat.gcd h (2 ^ 11) * Nat.gcd h (3 ^ 5) = h := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 2 ^ 11) (m := 3 ^ 5) (x := h) (by norm_num)).mpr
    norm_num at hdvd ⊢
    exact hdvd
  obtain ⟨a, ha, htwo⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp
      (Nat.gcd_dvd_right h (2 ^ 11))
  obtain ⟨b, hb, hthree⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
      (Nat.gcd_dvd_right h (3 ^ 5))
  exact ⟨a, ha, b, hb, hfactor ▸ congrArg₂ (· * ·) htwo hthree⟩

end FiveTransitive.Degree19

end CFSG
