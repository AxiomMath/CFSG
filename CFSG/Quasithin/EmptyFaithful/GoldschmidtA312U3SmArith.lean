module

import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.Quasithin.A312U3

set_option synthInstance.maxSize 256 in
theorem psl2_cases_378000 : ∀ q < 95, 4 ≤ q → q % 2 = 1 → q * (q ^ 2 - 1) / 2 ∣ 378000 →
    q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 15 := by
  decide

theorem psl2_cases_6048 : ∀ q < 60, 4 ≤ q → q % 2 = 1 → q * (q ^ 2 - 1) / 2 ∣ 6048 → q = 7 := by
  decide

theorem psl2_q_cases_378000 {q s : ℕ} (hq : 4 ≤ q) (ho : q % 2 = 1)
    (hs : 2 * s = q * (q ^ 2 - 1)) (h : s ∣ 378000) : q = 5 ∨ q = 7 ∨ q = 9 ∨ q = 15 := by
  have hs' : s = q * (q ^ 2 - 1) / 2 := by omega
  have hle : s ≤ 378000 := Nat.le_of_dvd (by norm_num) h
  have hq95 : q < 95 := by
    by_contra hge
    push Not at hge
    have : 95 * (95 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
    omega
  exact psl2_cases_378000 q hq95 hq ho (hs' ▸ h)

theorem psl2_q_cases_6048 {q s : ℕ} (hq : 4 ≤ q) (ho : q % 2 = 1)
    (hs : 2 * s = q * (q ^ 2 - 1)) (h : s ∣ 6048) : q = 7 := by
  have hs' : s = q * (q ^ 2 - 1) / 2 := by omega
  have hle : s ≤ 6048 := Nat.le_of_dvd (by norm_num) h
  have hq60 : q < 60 := by
    by_contra hge
    push Not at hge
    have : 60 * (60 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hge (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
    omega
  exact psl2_cases_6048 q hq60 hq ho (hs' ▸ h)

theorem psl3_false {q s N : ℕ} (hq : 3 ≤ q) (ho : q % 2 = 1) (hN : N = 6048 ∨ N = 378000)
    (hs : s * Nat.gcd 3 (q - 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) (hdvd : s ∣ N) : False := by
  have hN' : N ≤ 378000 := by rcases hN with rfl | rfl <;> norm_num
  have hle : s ≤ 378000 := (Nat.le_of_dvd (by rcases hN with rfl | rfl <;> norm_num) hdvd).trans hN'
  have hg3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
  have hq7 : q < 7 := by
    by_contra hge
    push Not at hge
    have h1 : 7 ^ 3 * ((7 ^ 2 - 1) * (7 ^ 3 - 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hge 3) (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 3) 1))
    have h2 : s * Nat.gcd 3 (q - 1) ≤ 378000 * 3 := Nat.mul_le_mul hle hg3
    omega
  interval_cases q
  · norm_num at hs
    have : s = 5616 := by omega
    subst this
    rcases hN with rfl | rfl <;> norm_num at hdvd
  · omega
  · norm_num at hs
    have : s = 372000 := by omega
    subst this
    rcases hN with rfl | rfl <;> norm_num at hdvd
  · omega

theorem psu3_small {q s N : ℕ} (hq : 3 ≤ q) (ho : q % 2 = 1) (hN : N = 6048 ∨ N = 378000)
    (hs : s * Nat.gcd 3 (q + 1) = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) (hdvd : s ∣ N) :
    (q = 3 ∧ N = 6048) ∨ (q = 5 ∧ N = 378000) := by
  have hN' : N ≤ 378000 := by rcases hN with rfl | rfl <;> norm_num
  have hle : s ≤ 378000 := (Nat.le_of_dvd (by rcases hN with rfl | rfl <;> norm_num) hdvd).trans hN'
  have hg3 : Nat.gcd 3 (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 _)
  have hq7 : q < 7 := by
    by_contra hge
    push Not at hge
    have h1 : 7 ^ 3 * ((7 ^ 2 - 1) * (7 ^ 3 + 1)) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hge 3) (Nat.mul_le_mul
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hge 2) 1)
        (Nat.add_le_add_right (Nat.pow_le_pow_left hge 3) 1))
    have h2 : s * Nat.gcd 3 (q + 1) ≤ 378000 * 3 := Nat.mul_le_mul hle hg3
    omega
  interval_cases q
  · norm_num at hs
    have : s = 6048 := by omega
    subst this
    rcases hN with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · norm_num at hdvd
  · omega
  · norm_num at hs
    have : s = 126000 := by omega
    subst this
    rcases hN with rfl | rfl
    · norm_num at hdvd
    · exact Or.inr ⟨rfl, rfl⟩
  · omega

theorem not_dvd_7920 {N : ℕ} (hN : N = 6048 ∨ N = 378000) : ¬ 7920 ∣ N := by
  rcases hN with rfl | rfl <;> norm_num

end CFSG.Quasithin.A312U3
