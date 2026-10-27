module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NQCore.D4

theorem two_pow_add_one_ne_prime_pow {p m a : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ha : a = 2 ∨ a = 3) : 2 ^ m + 1 ≠ p ^ a := by
  intro h
  obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := (hp.odd_of_ne_two (by omega))
  rcases ha with rfl | rfl
  · have h1 : 2 ^ m = (2 * r) * (2 * r + 2) := by
      have : 2 ^ m + 1 = (2 * r + 1) ^ 2 := h
      nlinarith
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (⟨2 * r + 2, h1⟩ : 2 * r ∣ 2 ^ m)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (⟨2 * r, by rw [h1]; ring⟩ : 2 * r + 2 ∣ 2 ^ m)
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
  · have h1 : 2 ^ m = (2 * r) * (4 * r ^ 2 + 6 * r + 3) := by
      have : 2 ^ m + 1 = (2 * r + 1) ^ 3 := h
      nlinarith
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (⟨2 * r, by rw [h1]; ring⟩ : 4 * r ^ 2 + 6 * r + 3 ∣ 2 ^ m)
    rcases k with _ | k
    · have : 0 < r := by omega
      nlinarith
    · have : 4 * r ^ 2 + 6 * r + 3 = 2 * 2 ^ k := by rw [hk]; ring
      omega

theorem not_dvd_pow_three_sub_one {p q d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hd : d = 1 ∨ d = 3) (h : p ∣ 1 + q ^ d) : ¬ p ∣ q ^ 3 - 1 := by
  have h3 : p ∣ q ^ 3 + 1 := by
    rcases hd with rfl | rfl
    · have h' : q + 1 ∣ q ^ 3 + 1 ^ 3 := Odd.nat_add_dvd_pow_add_pow q 1 (by decide)
      rw [one_pow] at h'
      rw [pow_one, add_comm] at h
      exact h.trans h'
    · rwa [add_comm] at h
  intro h'
  have h1 : p ∣ (q ^ 3 + 1) - (q ^ 3 - 1) := Nat.dvd_sub h3 h'
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  have e : (q ^ 3 + 1) - (q ^ 3 - 1) = 2 := by omega
  rw [e] at h1
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)

theorem false_of_dvd_of_dvd_mul {p a n d B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a = 2 ∨ a = 3)
    (hBp : ¬ p ∣ B) (h1 : 1 + (2 ^ n) ^ d ∣ p ^ a) (h2 : p ^ a ∣ B * (1 + (2 ^ n) ^ d)) :
    False := by
  have hcop : Nat.Coprime (p ^ a) B :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hBp)
  have h3 : p ^ a ∣ 1 + (2 ^ n) ^ d := hcop.dvd_of_dvd_mul_left h2
  have h4 : 1 + (2 ^ n) ^ d = p ^ a := Nat.dvd_antisymm h1 h3
  refine two_pow_add_one_ne_prime_pow (m := n * d) hp hp5 ha ?_
  rw [pow_mul, ← h4]
  omega

end CFSG.Quasithin.H13.NQCore.D4
