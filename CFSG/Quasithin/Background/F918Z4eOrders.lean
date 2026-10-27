module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Z4e

@[expose] def IsEvenPSL2Order (n : ℕ) : Prop :=
  n = 60 ∨ ∃ m : ℕ, 1 ≤ m ∧ n = 2 ^ m * ((2 ^ m) ^ 2 - 1)

theorem not_three_dvd_two_pow (m : ℕ) : ¬ 3 ∣ 2 ^ m := fun h => by
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem three_dvd_of_isEvenPSL2Order {n : ℕ} (h : IsEvenPSL2Order n) : 3 ∣ n := by
  rcases h with rfl | ⟨m, -, rfl⟩
  · norm_num
  · refine Dvd.dvd.mul_left ?_ _
    have h3 := not_three_dvd_two_pow m
    have h1 : (2 ^ m) ^ 2 % 3 = 1 := by
      have : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    have : 1 ≤ (2 ^ m) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega

theorem not_isEvenPSL2Order_suzuki (a : ℕ) :
    ¬ IsEvenPSL2Order (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 *
      (2 ^ (2 * a + 1) - 1)) := by
  intro h
  have h3 := three_dvd_of_isEvenPSL2Order h
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  generalize 2 ^ (2 * a + 1) = q at hq hq1 h3
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · omega
    · omega
  · omega

theorem not_isEvenPSL2Order_j1 : ¬ IsEvenPSL2Order 175560 := by
  rintro (h | ⟨m, hm, h⟩)
  · omega
  · by_cases hm10 : 10 ≤ m
    · have hN : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm10
      have h1 : 2 ^ 10 * ((2 ^ 10) ^ 2 - 1) ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
        Nat.mul_le_mul hN (Nat.sub_le_sub_right (Nat.pow_le_pow_left hN 2) 1)
      omega
    · interval_cases m <;> omega

theorem not_two_mul_le_succ {N : ℕ} (hN : 6 ≤ N) :
    ¬ 2 * (N * (N ^ 2 - 1)) ≤ (N + 1) * ((N + 1) ^ 2 - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, N = a + 6 := ⟨N - 6, by omega⟩
  have e1 : (a + 6) ^ 2 - 1 = (a + 5) * (a + 7) := by
    rw [show (a + 6) ^ 2 = (a + 5) * (a + 7) + 1 by ring]
    rfl
  have e2 : (a + 6 + 1) ^ 2 - 1 = (a + 6) * (a + 8) := by
    rw [show (a + 6 + 1) ^ 2 = (a + 6) * (a + 8) + 1 by ring]
    rfl
  rw [e1, e2]
  intro h
  nlinarith [Nat.zero_le a, Nat.zero_le (a ^ 2), Nat.zero_le (a ^ 3)]

theorem not_isEvenPSL2Order_of_two_mul_eq {p n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hn : 2 * n = p * (p ^ 2 - 1)) : ¬ IsEvenPSL2Order n := by
  have hbig : 7 * (7 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
    Nat.mul_le_mul hp7 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1)
  rintro (rfl | ⟨m, hm, rfl⟩)
  · omega
  · have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
    have hN2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hdvd : p ∣ 2 * (2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
      rw [hn]
      exact dvd_mul_right p _
    have hpN : ¬ p ∣ 2 ^ m := fun h => hp2 (hp.dvd_of_dvd_pow h)
    have hdvd2 : p ∣ (2 ^ m) ^ 2 - 1 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
      · exact absurd h hp2
      · rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
        · exact absurd h' hpN
        · exact h'
    generalize 2 ^ m = N at hN2 hn hdvd2 hpN
    have hfac : N ^ 2 - 1 = (N + 1) * (N - 1) := by
      obtain ⟨b, rfl⟩ : ∃ b, N = b + 1 := ⟨N - 1, by omega⟩
      rw [show (b + 1) ^ 2 = (b + 2) * b + 1 by ring]
      simp
    rw [hfac] at hdvd2
    have hle : p ≤ N + 1 := by
      rcases (Nat.Prime.dvd_mul hp).mp hdvd2 with h | h
      · exact Nat.le_of_dvd (by omega) h
      · have := Nat.le_of_dvd (by omega) h
        omega
    have hN6 : 6 ≤ N := by omega
    have h1 : p * (p ^ 2 - 1) ≤ (N + 1) * ((N + 1) ^ 2 - 1) :=
      Nat.mul_le_mul hle (Nat.sub_le_sub_right (Nat.pow_le_pow_left hle 2) 1)
    exact not_two_mul_le_succ hN6 (by rw [hn]; exact h1)

end CFSG.Quasithin.Z4e
