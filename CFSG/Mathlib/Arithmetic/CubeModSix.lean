module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG

theorem mod_six_eq_one_of_pow_three {n : ℕ} (h : n ^ 3 % 6 = 1) : n % 6 = 1 := by
  have h' : (n % 6) ^ 3 % 6 = 1 := by
    rw [← Nat.pow_mod]
    exact h
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 6 <;> simp_all

theorem mod_six_eq_five_of_pow_three {n : ℕ} (h : n ^ 3 % 6 = 5) : n % 6 = 5 := by
  have h' : (n % 6) ^ 3 % 6 = 5 := by
    rw [← Nat.pow_mod]
    exact h
  have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 6 <;> simp_all

theorem three_dvd_sub_one_of_mod_six_eq_one {n : ℕ} (h : n % 6 = 1) : 3 ∣ n - 1 := by
  omega

theorem three_dvd_succ_of_mod_six_eq_five {n : ℕ} (h : n % 6 = 5) : 3 ∣ n + 1 := by
  omega

theorem mod_three_eq_one_of_mod_six_eq_one {n : ℕ} (h : n % 6 = 1) : n % 3 = 1 := by
  omega

theorem mod_three_eq_two_of_mod_six_eq_five {n : ℕ} (h : n % 6 = 5) : n % 3 = 2 := by
  omega

theorem five_le_of_mod_six_eq_five {n : ℕ} (h : n % 6 = 5) : 5 ≤ n := by
  omega

theorem five_le_of_prime_of_pow_mod_six {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (h : p ^ f % 6 = 1 ∨ p ^ f % 6 = 5) : 5 ≤ p := by
  have hpne2 : p ≠ 2 := by
    rintro rfl
    have hmod : (2 ^ f % 6) % 2 = 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 6)]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : f ≠ 0))
    rcases h with h | h <;> rw [h] at hmod <;> norm_num at hmod
  have hpne3 : p ≠ 3 := by
    rintro rfl
    have hmod : (3 ^ f % 6) % 3 = 0 := by
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by omega : f ≠ 0))
    rcases h with h | h <;> rw [h] at hmod <;> norm_num at hmod
  have hpne4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  have hp2 : 2 ≤ p := hp.two_le
  omega

theorem val_pow_three_eq_one_of_eq_or_eq_sq {F : Type*} [Field F] {τ : F} (hτ : τ ^ 3 = 1) {e : Fˣ}
    (he : (e : F) = τ ∨ (e : F) = τ ^ 2) : (e : F) ^ 3 = 1 := by
  rcases he with h | h
  · rw [h]; exact hτ
  · rw [h, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hτ, one_pow]

theorem ne_one_of_val_eq_or_eq_sq {F : Type*} [Field F] {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {e : Fˣ} (he : (e : F) = τ ∨ (e : F) = τ ^ 2) : e ≠ 1 := by
  rintro rfl
  simp only [Units.val_one] at he
  rcases he with h | h
  · exact hτ1 h.symm
  · have h1 : τ * τ ^ 2 = 1 := by
      rw [← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, hτ]
    rw [← h, mul_one] at h1
    exact hτ1 h1

end CFSG

end
