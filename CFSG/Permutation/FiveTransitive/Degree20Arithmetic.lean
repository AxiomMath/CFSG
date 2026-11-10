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

namespace FiveTransitive.Degree20

abbrev SeventeenNormalizerRatio :=
  ↥(Nat.divisors 16)

abbrev NineteenNormalizerRatio :=
  ↥(Nat.divisors 18)

@[expose] def stabilizerFactorArithmeticPredicateZero
    (a : Fin 12) (b : Fin 7) : Prop :=
  let h := 2 ^ a.val * 3 ^ b.val
  ((11 * h) % 17 = 8 ∨ (11 * h) % 17 = 16) →
    ((13 * h) % 19 = 1 ∨
      (13 * h) % 19 = 2 ∨
      (13 * h) % 19 = 3 ∨
      (13 * h) % 19 = 6 ∨
      (13 * h) % 19 = 9 ∨
      (13 * h) % 19 = 18) →
    h = 3 ∨ h = 27 ∨ h = 54 ∨ h = 972 ∨
      h = 768 ∨ h = 248832

theorem stabilizer_factor_arithmetic_zero :
    ∀ a : Fin 12, ∀ b : Fin 7,
      stabilizerFactorArithmeticPredicateZero a b := by
  letI (a : Fin 12) (b : Fin 7) :
      Decidable (stabilizerFactorArithmeticPredicateZero a b) := by
    dsimp only [stabilizerFactorArithmeticPredicateZero]
    infer_instance
  letI : Decidable
      (∀ a : Fin 12, ∀ b : Fin 7,
        stabilizerFactorArithmeticPredicateZero a b) :=
    Fintype.decidableForallFintype
  decide

@[expose] def stabilizerFactorArithmeticPredicateOne
    (a : Fin 12) (b : Fin 7) : Prop :=
  let h := 2 ^ a.val * 3 ^ b.val * 5
  ((11 * h) % 17 = 8 ∨ (11 * h) % 17 = 16) →
    ((13 * h) % 19 = 1 ∨
      (13 * h) % 19 = 2 ∨
      (13 * h) % 19 = 3 ∨
      (13 * h) % 19 = 6 ∨
      (13 * h) % 19 = 9 ∨
      (13 * h) % 19 = 18) →
    h = 180 ∨ h = 360 ∨ h = 58320 ∨
      h = 116640 ∨ h = 5120

theorem stabilizer_factor_arithmetic_one :
    ∀ a : Fin 12, ∀ b : Fin 7,
      stabilizerFactorArithmeticPredicateOne a b := by
  letI (a : Fin 12) (b : Fin 7) :
      Decidable (stabilizerFactorArithmeticPredicateOne a b) := by
    dsimp only [stabilizerFactorArithmeticPredicateOne]
    infer_instance
  letI : Decidable
      (∀ a : Fin 12, ∀ b : Fin 7,
        stabilizerFactorArithmeticPredicateOne a b) :=
    Fintype.decidableForallFintype
  decide

@[expose] def stabilizerFactorArithmeticPredicateTwo
    (a : Fin 12) (b : Fin 7) : Prop :=
  let h := 2 ^ a.val * 3 ^ b.val * 25
  ((11 * h) % 17 = 8 ∨ (11 * h) % 17 = 16) →
    ((13 * h) % 19 = 1 ∨
      (13 * h) % 19 = 2 ∨
      (13 * h) % 19 = 3 ∨
      (13 * h) % 19 = 6 ∨
      (13 * h) % 19 = 9 ∨
      (13 * h) % 19 = 18) →
    h = 1200 ∨ h = 2400 ∨ h = 21600 ∨
      h = 388800 ∨ h = 777600

theorem stabilizer_factor_arithmetic_two :
    ∀ a : Fin 12, ∀ b : Fin 7,
      stabilizerFactorArithmeticPredicateTwo a b := by
  letI (a : Fin 12) (b : Fin 7) :
      Decidable (stabilizerFactorArithmeticPredicateTwo a b) := by
    dsimp only [stabilizerFactorArithmeticPredicateTwo]
    infer_instance
  letI : Decidable
      (∀ a : Fin 12, ∀ b : Fin 7,
        stabilizerFactorArithmeticPredicateTwo a b) :=
    Fintype.decidableForallFintype
  decide

@[expose] def stabilizerFactorArithmeticPredicateThree
    (a : Fin 12) (b : Fin 7) : Prop :=
  let h := 2 ^ a.val * 3 ^ b.val * 125
  ((11 * h) % 17 = 8 ∨ (11 * h) % 17 = 16) →
    ((13 * h) % 19 = 1 ∨
      (13 * h) % 19 = 2 ∨
      (13 * h) % 19 = 3 ∨
      (13 * h) % 19 = 6 ∨
      (13 * h) % 19 = 9 ∨
      (13 * h) % 19 = 18) →
    h = 144000 ∨ h = 46656000

theorem stabilizer_factor_arithmetic_three :
    ∀ a : Fin 12, ∀ b : Fin 7,
      stabilizerFactorArithmeticPredicateThree a b := by
  letI (a : Fin 12) (b : Fin 7) :
      Decidable (stabilizerFactorArithmeticPredicateThree a b) := by
    dsimp only [stabilizerFactorArithmeticPredicateThree]
    infer_instance
  letI : Decidable
      (∀ a : Fin 12, ∀ b : Fin 7,
        stabilizerFactorArithmeticPredicateThree a b) :=
    Fintype.decidableForallFintype
  decide

theorem seventeen_normalizer_ratio_cases
    (r : SeventeenNormalizerRatio) (hr : 6 ≤ r.val) :
    r.val = 8 ∨ r.val = 16 := by
  have hrdvd : r.val ∣ 16 :=
    (Nat.mem_divisors.mp r.prop).1
  have hrle : r.val ≤ 16 :=
    Nat.le_of_dvd (by norm_num) hrdvd
  interval_cases r.val
  all_goals try norm_num at hrdvd
  all_goals try norm_num at hr
  all_goals norm_num

theorem exists_two_three_five_power_of_dvd_one_hundred_eighty_six_million
    {h : ℕ} (hdvd : h ∣ 186624000) :
    ∃ a ≤ 11, ∃ b ≤ 6, ∃ c ≤ 3,
      h = 2 ^ a * 3 ^ b * 5 ^ c := by
  let r := Nat.gcd h (3 ^ 6 * 5 ^ 3)
  have hfactorOuter :
      Nat.gcd h (2 ^ 11) * r = h := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 2 ^ 11) (m := 3 ^ 6 * 5 ^ 3)
        (x := h) (by norm_num)).mpr
    norm_num at hdvd ⊢
    exact hdvd
  have hrDvd : r ∣ 3 ^ 6 * 5 ^ 3 :=
    Nat.gcd_dvd_right h _
  have hfactorInner :
      Nat.gcd r (3 ^ 6) * Nat.gcd r (5 ^ 3) = r := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 3 ^ 6) (m := 5 ^ 3)
        (x := r) (by norm_num)).mpr
    exact hrDvd
  obtain ⟨a, ha, htwo⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp
      (Nat.gcd_dvd_right h (2 ^ 11))
  obtain ⟨b, hb, hthree⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
      (Nat.gcd_dvd_right r (3 ^ 6))
  obtain ⟨c, hc, hfive⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
      (Nat.gcd_dvd_right r (5 ^ 3))
  refine ⟨a, ha, b, hb, c, hc, ?_⟩
  calc
    h = Nat.gcd h (2 ^ 11) * r :=
      hfactorOuter.symm
    _ = 2 ^ a *
        (Nat.gcd r (3 ^ 6) * Nat.gcd r (5 ^ 3)) := by
      rw [htwo, hfactorInner]
    _ = 2 ^ a * 3 ^ b * 5 ^ c := by
      rw [hthree, hfive, Nat.mul_assoc]

end FiveTransitive.Degree20

end CFSG
