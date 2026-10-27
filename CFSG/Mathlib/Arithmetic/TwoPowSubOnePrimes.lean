module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

theorem not_exists_orderOf_two_eq_two_pow_of_odd {n r : ℕ} (hn : Odd n) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : ¬ ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k := by
  rintro ⟨k, hk⟩
  have h2n : (2 : ZMod r) ^ n = 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow' n 1), sub_eq_zero] at hrn
    simpa using hrn
  have hdvd : 2 ^ k ∣ n := by
    rw [← hk]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2n
  have hk0 : k = 0 := by
    by_contra hk0
    have hodd : Odd (2 ^ k) := Odd.of_dvd_nat hn hdvd
    have heven : Even (2 ^ k) := even_two.pow_of_ne_zero hk0
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  subst hk0
  have htwo : (2 : ZMod r) = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
  have hsub : ((2 - 1 : ℕ) : ZMod r) = 0 := by
    rw [Nat.cast_sub (by norm_num : 1 ≤ 2)]
    have htwo' : ((2 : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) := by simpa using htwo
    rw [htwo', sub_self]
  have hr1 : r ∣ 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 - 1) r).mp hsub
    simpa using h
  have hle : r ≤ 1 := Nat.le_of_dvd (by norm_num) hr1
  have hr2 : 2 ≤ r := hr.two_le
  omega

theorem exists_prime_ne_two_ne_three_dvd_two_pow_sub_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ∣ 2 ^ n - 1 := by
  by_contra hne
  push Not at hne
  have hm0 : 2 ^ n - 1 ≠ 0 := by
    have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hodd : Odd (2 ^ n - 1) := by
    have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
    exact Nat.Even.sub_odd (Nat.one_le_pow' n 1) he odd_one
  have h3 : ∀ d, d.Prime → d ∣ 2 ^ n - 1 → d = 3 := by
    intro d hd hdn
    have hdlt : d < 5 := by
      by_contra h
      exact hne d hd (by omega) (by omega) hdn
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdn)
    interval_cases d
    · exact absurd hd Nat.not_prime_zero
    · exact absurd hd Nat.not_prime_one
    · exact absurd rfl hd2
    · rfl
    · exact absurd hd (by decide)
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hm0 (fun {d} hd hdn => h3 d hd hdn)
  have h8 : 2 ^ n % 8 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [pow_add]
    norm_num
  have h3mod : ∀ a : ℕ, 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
    intro a
    induction a with
    | zero => left; norm_num
    | succ a ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> rw [h] <;> norm_num
  rcases h3mod (2 ^ n - 1).primeFactorsList.length with h | h <;> omega

theorem exists_prime_five_le_dvd_two_pow_sub_one {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ n - 1 := by
  obtain ⟨r, hr, hr2, hr3, hrd⟩ := exists_prime_ne_two_ne_three_dvd_two_pow_sub_one hn
  exact ⟨r, hr, hr.five_le_of_ne_two_of_ne_three hr2 hr3, hrd⟩

end CFSG
