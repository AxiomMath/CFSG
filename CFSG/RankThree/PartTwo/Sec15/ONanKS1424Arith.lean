module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Zify
public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

theorem three_pow_mod_eight (a : ℕ) :
    (3 ^ a % 8 = 1 ∧ Even a) ∨ (3 ^ a % 8 = 3 ∧ Odd a) := by
  induction a with
  | zero => exact Or.inl ⟨by norm_num, ⟨0, rfl⟩⟩
  | succ a ih =>
    rw [pow_succ]
    rcases ih with ⟨h, he⟩ | ⟨h, ho⟩
    · exact Or.inr ⟨by omega, he.add_one⟩
    · exact Or.inl ⟨by omega, ho.add_one⟩

theorem exists_prime_dvd_pow_two_sub {n : ℕ} (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ 2 ^ n - 1 := by
  by_contra hno
  push Not at hno
  have h8 : 8 ∣ 2 ^ n := by
    have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    simpa using this
  have h16 : 16 ≤ 2 ^ n := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hN0 : 2 ^ n - 1 ≠ 0 := by omega
  have hodd : ¬ 2 ∣ 2 ^ n - 1 := by omega
  have hN3 : 2 ^ n - 1 = 3 ^ (2 ^ n - 1).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd hN0 (fun {d} hd hdN => ?_)
    have hd3 : d ≤ 3 := by
      by_contra h
      exact hno d hd (by omega) hdN
    have := hd.two_le
    interval_cases d
    · exact absurd hdN hodd
    · rfl
  have := three_pow_mod_eight (2 ^ n - 1).primeFactorsList.length
  rw [← hN3] at this
  omega

theorem exists_prime_dvd_pow_two_add {n : ℕ} (hn : 4 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ 2 ^ n + 1 := by
  by_contra hno
  push Not at hno
  have h8 : 8 ∣ 2 ^ n := by
    have : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    simpa using this
  have h16 : 16 ≤ 2 ^ n := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : ¬ 2 ∣ 2 ^ n + 1 := by omega
  have hN3 : 2 ^ n + 1 = 3 ^ (2 ^ n + 1).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (fun {d} hd hdN => ?_)
    have hd3 : d ≤ 3 := by
      by_contra h
      exact hno d hd (by omega) hdN
    have := hd.two_le
    interval_cases d
    · exact absurd hdN hodd
    · rfl
  set a := (2 ^ n + 1).primeFactorsList.length with ha
  have hmod := three_pow_mod_eight a
  rw [← hN3] at hmod
  obtain ⟨b, hb⟩ : Even a := by
    rcases hmod with ⟨-, he⟩ | ⟨h, -⟩
    · exact he
    · omega
  have h2n : 2 ^ n = (3 ^ b - 1) * (3 ^ b + 1) := by
    have h3b : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    have : 3 ^ a = 3 ^ b * 3 ^ b := by rw [hb, ← two_mul, pow_mul']; ring
    have h' : 2 ^ n + 1 = 3 ^ b * 3 ^ b := by rw [hN3, this]
    zify [h3b]
    have h'' : (2 : ℤ) ^ n + 1 = 3 ^ b * 3 ^ b := by exact_mod_cast h'
    linear_combination h''
  have hb1 : 3 ^ b - 1 ∣ 2 ^ n := ⟨3 ^ b + 1, h2n⟩
  have hb2 : 3 ^ b + 1 ∣ 2 ^ n := ⟨3 ^ b - 1, by rw [h2n, mul_comm]⟩
  obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb1
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hb2
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at h2n
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hi1 : i ≠ 0 := by
    rintro rfl
    simp at hi'
    omega
  have hj2 : 2 ≤ j := by
    by_contra h
    have : j ≤ 1 := by omega
    interval_cases j
    · simp at hj'
    · simp at hj'
      omega
  by_cases hi2 : 2 ≤ i
  · have h4i : 4 ∣ 2 ^ i := by
      have : 2 ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 hi2
      simpa using this
    have h4j : 4 ∣ 2 ^ j := by
      have : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj2
      simpa using this
    omega
  · have hi1' : i = 1 := by omega
    subst hi1'
    have hb3 : 3 ^ b = 3 := by omega
    rw [hb3] at h2n
    omega

end CFSG.RankThree.PartTwo.Sec15.KS1424
