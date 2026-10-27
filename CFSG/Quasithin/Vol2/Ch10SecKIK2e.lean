module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem dvd_of_b56Card {N : ℕ} (h : B56Card N) (h16 : ¬ 16 ∣ N) : N ∣ 7560 := by
  have h16p : ∀ m : ℕ, 4 ≤ m → (16 : ℕ) ∣ 2 ^ m := fun m hm => by
    have := Nat.pow_dvd_pow 2 hm
    norm_num at this
    exact this
  rcases h with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | rfl | rfl | rfl | rfl |
      rfl | rfl
  · rcases Nat.lt_or_ge n 4 with h4 | h4
    · interval_cases n <;> norm_num
    · exact absurd (dvd_mul_of_dvd_left (h16p n h4) _) h16
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · interval_cases n
      norm_num
    · rw [← pow_mul] at h16
      exact absurd (dvd_mul_of_dvd_left (h16p (n * 3) (by omega)) _) h16
  · rw [← pow_mul] at h16
    exact absurd (dvd_mul_of_dvd_left (h16p (n * 4) (by omega)) _) h16
  · rw [← pow_mul] at h16
    exact absurd (dvd_mul_of_dvd_left (h16p (n * 6) (by omega)) _) h16
  · norm_num
  · norm_num
  · norm_num
  · exact absurd (by norm_num) h16
  · exact absurd (by norm_num) h16
  · exact absurd (by norm_num) h16

theorem le_seven_of_dvd {p : ℕ} (hp : p.Prime) (h : p ∣ 7560) : p ≤ 7 := by
  have e : (7560 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 * 7 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)).trans (by norm_num)
      · exact (Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)).trans (by norm_num)
    · exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)
  · exact Nat.le_of_dvd (by norm_num) h

theorem not_sixteen_dvd {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5) : ¬ 16 ∣ p * (p ^ 2 - 1) := by
  have h16 : p % 16 = 3 ∨ p % 16 = 5 ∨ p % 16 = 11 ∨ p % 16 = 13 := by omega
  have hsq : p ^ 2 % 16 = 9 := by
    rw [Nat.pow_mod]
    rcases h16 with h | h | h | h <;> rw [h]
  have h1 : (p ^ 2 - 1) % 16 = 8 := by
    generalize p ^ 2 = q at hsq ⊢
    omega
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, h1]
  rcases h16 with h | h | h | h <;> rw [h] <;> norm_num

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
