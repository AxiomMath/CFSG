module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.FiniteField

theorem pow_three_ne_of_not_nine_dvd {K : Type*} [Field K] [Finite K]
    (h9 : ¬ 9 ∣ Nat.card K - 1) {ζ : K} (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (μ : K) :
    μ ^ 3 ≠ ζ := by
  intro hμ
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    rw [← hμ, zero_pow (by norm_num)] at hζ3
    exact zero_ne_one hζ3
  set u := Units.mk0 μ hμ0 with hu
  have hu9 : u ^ 9 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
      show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hμ, hζ3]
  have hu3 : u ^ 3 ≠ 1 := by
    intro h
    apply hζ1
    have h' := congrArg Units.val h
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, hμ] at h'
  have hord : orderOf u = 9 := by
    have hd : orderOf u ∣ 3 ^ 2 := by simpa using orderOf_dvd_of_pow_eq_one hu9
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    interval_cases k
    · exfalso
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hu3 (by rw [hk, one_pow])
    · exfalso
      rw [pow_one] at hk
      exact hu3 (by rw [← hk]; exact pow_orderOf_eq_one u)
    · rw [hk]; norm_num
  have hdvd : orderOf u ∣ Nat.card Kˣ := orderOf_dvd_natCard u
  rw [hord, Nat.card_units] at hdvd
  exact h9 hdvd

end CFSG.FiniteField
