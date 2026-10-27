module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NQCore.G2

theorem two_pow_add_one_ne_prime_pow {p n j : ℕ} (hp5 : 5 ≤ p) (hodd : Odd p) (hj : 2 ≤ j)
    (hj3 : j ≤ 3) : 2 ^ n + 1 ≠ p ^ j := by
  intro h
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := hodd
  have hj' : j = 2 ∨ j = 3 := by omega
  rcases hj' with rfl | rfl
  ·
    have h1 : 2 ^ n = (2 * r) * (2 * r + 2) := by
      have : 2 ^ n + 1 = (2 * r + 1) ^ 2 := h
      nlinarith
    have hd1 : 2 * r ∣ 2 ^ n := ⟨2 * r + 2, h1⟩
    have hd2 : 2 * r + 2 ∣ 2 ^ n := ⟨2 * r, by rw [h1]; ring⟩
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
    have hi2 : 2 ≤ i := by
      by_contra hlt
      push Not at hlt
      interval_cases i <;> omega
    have h4 : 4 ∣ 2 * r := by
      rw [hi]
      exact (pow_dvd_pow 2 hi2 : 2 ^ 2 ∣ 2 ^ i)
    rcases k with _ | _ | k
    · omega
    · omega
    · have : 4 ∣ 2 * r + 2 := by
        rw [hk]
        exact Dvd.intro (2 ^ k) (by ring)
      omega
  ·
    have h1 : 2 ^ n = (2 * r) * (4 * r ^ 2 + 6 * r + 3) := by
      have : 2 ^ n + 1 = (2 * r + 1) ^ 3 := h
      nlinarith
    have hd : 4 * r ^ 2 + 6 * r + 3 ∣ 2 ^ n := ⟨2 * r, by rw [h1]; ring⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    rcases k with _ | k
    · have : 0 < r := by omega
      nlinarith
    · have : 4 * r ^ 2 + 6 * r + 3 = 2 * 2 ^ k := by rw [hk]; ring
      omega

end CFSG.Quasithin.H13.NQCore.G2
