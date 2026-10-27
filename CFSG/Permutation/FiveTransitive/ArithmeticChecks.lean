module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.ArithmeticChecks

theorem le_seven_of_dvd_5880
    (k : ℕ) (hk : k ∣ 5880)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (h5 : ¬ 5 ∣ k)
    (h49 : ¬ 49 ∣ k) : k ≤ 7 := by
  have hc2 : Nat.Coprime k 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 : Nat.Coprime k 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hc5 : Nat.Coprime k 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm
  have hc : Nat.Coprime k (2 ^ 3 * 3 * 5) :=
    ((hc2.pow_right 3).mul_right hc3).mul_right hc5
  change Nat.Coprime k 120 at hc
  have hk49 : k ∣ 7 ^ 2 := hc.dvd_mul_left.mp hk
  obtain ⟨a, ha, hka⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hk49
  interval_cases a <;> norm_num at hka <;> omega

theorem le_seven_of_dvd_1176
    (k : ℕ) (hk : k ∣ 1176)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (h49 : ¬ 49 ∣ k) : k ≤ 7 := by
  apply le_seven_of_dvd_5880 k (hk.trans (by decide)) h2 h3 _ h49
  intro h5
  exact (by decide : ¬ 5 ∣ 1176) (h5.trans hk)

theorem le_twentyFive_of_dvd_3600
    (k : ℕ) (hk : k ∣ 3600) (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) : k ≤ 25 := by
  have hc2 : Nat.Coprime k 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 : Nat.Coprime k 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hc : Nat.Coprime k (2 ^ 4 * 3 ^ 2) := (hc2.pow_right 4).mul_right (hc3.pow_right 2)
  change Nat.Coprime k 144 at hc
  have hk25 : k ∣ 25 := hc.dvd_mul_left.mp hk
  exact Nat.le_of_dvd (by decide) hk25

theorem le_seven_of_dvd_35280
    (k : ℕ) (hk : k ∣ 35280)
    (h2 : ¬ 2 ∣ k) (h3 : ¬ 3 ∣ k) (h5 : ¬ 5 ∣ k)
    (h49 : ¬ 49 ∣ k) : k ≤ 7 := by
  have hc2 : Nat.Coprime k 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hc3 : Nat.Coprime k 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hc5 : Nat.Coprime k 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm
  have hc : Nat.Coprime k (2 ^ 4 * 3 ^ 2 * 5) :=
    ((hc2.pow_right 4).mul_right (hc3.pow_right 2)).mul_right hc5
  change Nat.Coprime k 720 at hc
  have hk49 : k ∣ 7 ^ 2 := hc.dvd_mul_left.mp hk
  obtain ⟨a, ha, hka⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hk49
  interval_cases a <;> norm_num at hka <;> omega

end FiveTransitive.ArithmeticChecks

end CFSG
