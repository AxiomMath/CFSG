module

public import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.RankThree.PartTwo.Sec20

theorem divisors_105 : Nat.divisors 105 = {1, 3, 5, 7, 15, 21, 35, 105} := by decide

theorem eq_of_dvd_105 {d : ℕ} (hd : d ∣ 105) :
    d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 15 ∨ d = 21 ∨ d = 35 ∨ d = 105 := by
  have hmem : d ∈ Nat.divisors 105 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  rw [divisors_105] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

theorem mem_of_forall_odd_dvd_dvd_105 {q : ℕ} (hq : Odd q)
    (h1 : ∀ n, Odd n → n ∣ q - 1 → n ∣ 105) (h2 : ∀ n, Odd n → n ∣ q + 1 → n ∣ 105) :
    q = 1 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 15 ∨ q = 29 ∨ q = 31 ∨
      q = 41 := by
  obtain ⟨k, rfl⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  ·
    have hd := h2 (2 * j + 1) (odd_two_mul_add_one j) ⟨2, by ring⟩
    rcases eq_of_dvd_105 hd with h | h | h | h | h | h | h | h
    · obtain rfl : j = 0 := by omega
      simp
    · obtain rfl : j = 1 := by omega
      simp
    · obtain rfl : j = 2 := by omega
      simp
    · obtain rfl : j = 3 := by omega
      simp
    · obtain rfl : j = 7 := by omega
      simp
    · obtain rfl : j = 10 := by omega
      simp
    · obtain rfl : j = 17 := by omega
      exact absurd (h1 17 (by decide) (by norm_num)) (by norm_num)
    · obtain rfl : j = 52 := by omega
      exact absurd (h1 13 (by decide) (by norm_num)) (by norm_num)
  ·
    have hd := h1 (2 * j + 1) (odd_two_mul_add_one j) ⟨2, by omega⟩
    rcases eq_of_dvd_105 hd with h | h | h | h | h | h | h | h
    · obtain rfl : j = 0 := by omega
      simp
    · obtain rfl : j = 1 := by omega
      simp
    · obtain rfl : j = 2 := by omega
      simp
    · obtain rfl : j = 3 := by omega
      simp
    · obtain rfl : j = 7 := by omega
      simp
    · obtain rfl : j = 10 := by omega
      exact absurd (h2 11 (by decide) (by norm_num)) (by norm_num)
    · obtain rfl : j = 17 := by omega
      exact absurd (h2 9 (by decide) (by norm_num)) (by norm_num)
    · obtain rfl : j = 52 := by omega
      exact absurd (h2 53 (by decide) (by norm_num)) (by norm_num)

theorem exists_odd_dvd_pow_add_one_not_dvd_105 {b k : ℕ} (hb : b = 5 ∨ b = 7) (hk : 2 ≤ k) :
    ∃ n, Odd n ∧ n ∣ b ^ k + 1 ∧ ¬ n ∣ 105 := by
  by_contra hall
  push Not at hall
  have key : ∀ c d : ℕ, b ^ k + 1 = c * d → Odd d → b ^ k + 1 ≤ c * 105 := by
    intro c d hcd hd
    have h105 := hall d hd ⟨c, by rw [hcd, mul_comm]⟩
    have hd105 := Nat.le_of_dvd (by norm_num) h105
    rw [hcd]
    exact Nat.mul_le_mul_left c hd105
  rcases hb with rfl | rfl
  ·
    have h4 : (5 ^ k + 1) % 4 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod]
      norm_num
    obtain ⟨m, hm⟩ : ∃ m, 5 ^ k + 1 = 2 * (2 * m + 1) := ⟨(5 ^ k + 1) / 4, by omega⟩
    have hle := key 2 (2 * m + 1) hm (odd_two_mul_add_one m)
    have hk3 : k ≤ 3 := by
      by_contra h
      have h1 : 5 ^ 4 ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : (5 : ℕ) ^ 4 = 625 := by norm_num
      omega
    interval_cases k
    · exact absurd (hall 13 (by decide) (by norm_num)) (by norm_num)
    · exact absurd (hall 63 (by decide) (by norm_num)) (by norm_num)
  · rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    ·
      have h4 : (7 ^ (j + j) + 1) % 4 = 2 := by
        rw [← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
        norm_num
      obtain ⟨m, hm⟩ : ∃ m, 7 ^ (j + j) + 1 = 2 * (2 * m + 1) :=
        ⟨(7 ^ (j + j) + 1) / 4, by omega⟩
      have hle := key 2 (2 * m + 1) hm (odd_two_mul_add_one m)
      have hj : j ≤ 1 := by
        by_contra h
        have h1 : 7 ^ 4 ≤ 7 ^ (j + j) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : (7 : ℕ) ^ 4 = 2401 := by norm_num
        omega
      interval_cases j
      · omega
      · exact absurd (hall 25 (by decide) (by norm_num)) (by norm_num)
    ·
      have h16 : (7 ^ (2 * j + 1) + 1) % 16 = 8 := by
        rw [pow_succ, pow_mul, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
        norm_num
      obtain ⟨m, hm⟩ : ∃ m, 7 ^ (2 * j + 1) + 1 = 8 * (2 * m + 1) :=
        ⟨(7 ^ (2 * j + 1) + 1) / 16, by omega⟩
      have hle := key 8 (2 * m + 1) hm (odd_two_mul_add_one m)
      have hj : j ≤ 1 := by
        by_contra h
        have h1 : 16807 ≤ 7 ^ (2 * j + 1) := by
          calc 16807 = 7 ^ 5 := by norm_num
            _ ≤ 7 ^ (2 * j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact absurd ((Nat.add_le_add_right h1 1).trans hle) (by norm_num)
      interval_cases j
      · omega
      · exact absurd (hall 43 (by decide) (by norm_num)) (by norm_num)

end CFSG.RankThree.PartTwo.Sec20
