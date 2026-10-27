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

namespace FiveTransitive.Degree24

@[expose] def stabilizerFactorArithmeticPredicate
    (a : Fin 13) (b : Fin 7) (c : Fin 3) (d : Fin 2) :
    Prop :=
  let h :=
    2 ^ a.val * 3 ^ b.val * 5 ^ c.val * 7 ^ d.val
  (h % 23 = 15 ∨ h % 23 = 2 ∨ h % 23 = 4) →
    (h % 11 = 1 ∨ h % 11 = 3 ∨ h % 11 = 4 ∨
      h % 11 = 5 ∨ h % 11 = 6 ∨ h % 11 = 8) →
    h = 25 ∨ h = 15 ∨ h = 27 ∨ h = 567 ∨
    h = 50 ∨ h = 1050 ∨ h = 4 ∨ h = 140 ∨
    h = 324 ∨ h = 8100 ∨ h = 280 ∨ h = 600 ∨
    h = 360 ∨ h = 13608 ∨ h = 48 ∨ h = 1200 ∨
    h = 97200 ∨ h = 96 ∨ h = 3360 ∨ h = 2016 ∨
    h = 194400 ∨ h = 4082400 ∨ h = 14400 ∨
    h = 8640 ∨ h = 1152 ∨ h = 1088640 ∨
    h = 2332800 ∨ h = 1280 ∨ h = 2304 ∨
    h = 48384 ∨ h = 4665600 ∨ h = 89600 ∨
    h = 13063680 ∨ h = 27648 ∨ h = 691200 ∨
    h = 26127360 ∨ h = 51200 ∨ h = 30720 ∨
    h = 1161216 ∨ h = 4096 ∨ h = 102400 ∨
    h = 8294400

theorem stabilizer_factor_arithmetic :
    ∀ a : Fin 13, ∀ b : Fin 7,
      ∀ c : Fin 3, ∀ d : Fin 2,
        stabilizerFactorArithmeticPredicate a b c d := by
  letI (a : Fin 13) (b : Fin 7)
      (c : Fin 3) (d : Fin 2) :
      Decidable
        (stabilizerFactorArithmeticPredicate a b c d) := by
    dsimp only [stabilizerFactorArithmeticPredicate]
    infer_instance
  letI : Decidable
      (∀ a : Fin 13, ∀ b : Fin 7,
        ∀ c : Fin 3, ∀ d : Fin 2,
          stabilizerFactorArithmeticPredicate a b c d) :=
    Fintype.decidableForallFintype
  decide

theorem exists_two_three_five_seven_power_of_dvd
    {h : ℕ} (hdvd : h ∣ 522547200) :
    ∃ a ≤ 12, ∃ b ≤ 6, ∃ c ≤ 2, ∃ d ≤ 1,
      h = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  let r := Nat.gcd h (3 ^ 6 * (5 ^ 2 * 7))
  have hfactorOuter :
      Nat.gcd h (2 ^ 12) * r = h := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 2 ^ 12) (m := 3 ^ 6 * (5 ^ 2 * 7))
        (x := h) (by norm_num)).mpr
    norm_num at hdvd ⊢
    exact hdvd
  have hrDvd : r ∣ 3 ^ 6 * (5 ^ 2 * 7) :=
    Nat.gcd_dvd_right h _
  let t := Nat.gcd r (5 ^ 2 * 7)
  have hfactorMiddle :
      Nat.gcd r (3 ^ 6) * t = r := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 3 ^ 6) (m := 5 ^ 2 * 7)
        (x := r) (by norm_num)).mpr
    exact hrDvd
  have htDvd : t ∣ 5 ^ 2 * 7 :=
    Nat.gcd_dvd_right r _
  have hfactorInner :
      Nat.gcd t (5 ^ 2) * Nat.gcd t 7 = t := by
    apply
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime
        (n := 5 ^ 2) (m := 7)
        (x := t) (by norm_num)).mpr
    exact htDvd
  obtain ⟨a, ha, htwo⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp
      (Nat.gcd_dvd_right h (2 ^ 12))
  obtain ⟨b, hb, hthree⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp
      (Nat.gcd_dvd_right r (3 ^ 6))
  obtain ⟨c, hc, hfive⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
      (Nat.gcd_dvd_right t (5 ^ 2))
  obtain ⟨d, hd, hseven⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp
      (show Nat.gcd t 7 ∣ 7 ^ 1 by
        simpa using Nat.gcd_dvd_right t 7)
  refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
  calc
    h = Nat.gcd h (2 ^ 12) * r :=
      hfactorOuter.symm
    _ = 2 ^ a *
        (Nat.gcd r (3 ^ 6) * t) := by
      rw [htwo, hfactorMiddle]
    _ = 2 ^ a * 3 ^ b *
        (Nat.gcd t (5 ^ 2) * Nat.gcd t 7) := by
      rw [hthree, hfactorInner]
      ring
    _ = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
      rw [hfive, hseven]
      ring

end FiveTransitive.Degree24

end CFSG
