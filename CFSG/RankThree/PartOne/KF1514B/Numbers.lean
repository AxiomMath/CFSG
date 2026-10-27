module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

public section

namespace CFSG.RankThree.PartOne.KF1514B

section Numbers

theorem not_dvd_96 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : ¬ p ∣ 96 := by
  intro h
  have h' : p ∣ 2 ^ 5 * 3 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h3
  · have := hp.dvd_of_dvd_pow h2
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    omega

theorem order_factor_three (r : ℕ) :
    (r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * (((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1) * ((r + 1) ^ 6 - 1)) =
      r ^ 3 * ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * ((r + 2) ^ 3 * (r ^ 2 + 2 * r + 2) *
        (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
  have e2 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e4 : (r + 1) ^ 4 - 1 = r * (r + 2) * (r ^ 2 + 2 * r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e6 : (r + 1) ^ 6 - 1 = r * (r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e2, e4, e6]
  ring

theorem order_factor_four (r : ℕ) :
    (r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * (((r + 1) ^ 2 - 1) * ((r + 1) ^ 4 - 1) * ((r + 1) ^ 6 - 1)) =
      (r + 2) ^ 3 * ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * (r ^ 3 * (r ^ 2 + 2 * r + 2) *
        (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
  have e2 : (r + 1) ^ 2 - 1 = r * (r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e4 : (r + 1) ^ 4 - 1 = r * (r + 2) * (r ^ 2 + 2 * r + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e6 : (r + 1) ^ 6 - 1 = r * (r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e2, e4, e6]
  ring

theorem not_dvd_cofactor_three {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {r : ℕ} (hr : p ∣ r) :
    ¬ p ∣ ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * ((r + 2) ^ 3 * (r ^ 2 + 2 * r + 2) *
        (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
  intro h
  have hz : ((r : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff r p).2 hr
  have h96 : ((96 : ℕ) : ZMod p) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at this
    rw [hz] at this
    norm_num at this ⊢
    exact this
  exact not_dvd_96 hp h5 ((ZMod.natCast_eq_zero_iff 96 p).1 h96)

theorem not_dvd_cofactor_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {r : ℕ} (hr : p ∣ r + 2) :
    ¬ p ∣ ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) * (r ^ 3 * (r ^ 2 + 2 * r + 2) *
        (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
  intro h
  have hz : ((r : ℕ) : ZMod p) = -2 := by
    have := (ZMod.natCast_eq_zero_iff (r + 2) p).2 hr
    push_cast at this
    linear_combination this
  have h96 : ((96 : ℕ) : ZMod p) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    push_cast at this
    rw [hz] at this
    norm_num at this ⊢
    exact this
  exact not_dvd_96 hp h5 ((ZMod.natCast_eq_zero_iff 96 p).1 h96)

end Numbers

end CFSG.RankThree.PartOne.KF1514B
