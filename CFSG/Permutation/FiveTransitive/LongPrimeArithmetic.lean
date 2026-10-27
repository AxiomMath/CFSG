module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Data.Nat.Factorization.Defs

public section

namespace CFSG

namespace FiveTransitive.LongPrimeArithmetic

theorem factorization_prime_mul_once
    (p a h : ℕ) (hp : Nat.Prime p) (ha : ¬p ∣ a) (hh : ¬p ∣ h) :
    (p * a * h).factorization p = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (dvd_zero p)
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hh (dvd_zero p)
  have hmul : ¬p ∣ a * h := by
    intro hd
    rcases hp.dvd_mul.mp hd with hd | hd
    · exact ha hd
    · exact hh hd
  rw [Nat.mul_assoc, Nat.factorization_mul hp.ne_zero (Nat.mul_ne_zero ha0 hh0),
    Finsupp.add_apply, hp.factorization, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hmul]

private theorem divisor_twenty_two_cases (r : ℕ) (hr : r ∣ 22) :
    r = 1 ∨ r = 2 ∨ r = 11 ∨ r = 22 := by
  have hle : r ≤ 22 := Nat.le_of_dvd (by omega) hr
  interval_cases r
  all_goals norm_num at hr
  all_goals omega

theorem degree_twenty_five_residue_pairs
    (h r s : ℕ) (hr : r ∣ 22) (hs : s ∣ 22)
    (hlocal : (2 * h) % 23 = r % 23)
    (hglobal : (4 * h) % 23 = s % 23) :
    (r = 1 ∧ s = 2) ∨ (r = 11 ∧ s = 22) := by
  rcases divisor_twenty_two_cases r hr with rfl | rfl | rfl | rfl
  all_goals rcases divisor_twenty_two_cases s hs with rfl | rfl | rfl | rfl
  all_goals norm_num at hlocal hglobal
  all_goals omega

theorem degree_twenty_six_residue_impossible
    (h r s : ℕ) (hr : r ∣ 22) (hs : s ∣ 22)
    (hlocal : (22 * h) % 23 = r % 23)
    (hglobal : (17 * h) % 23 = s % 23) : False := by
  rcases divisor_twenty_two_cases r hr with rfl | rfl | rfl | rfl
  all_goals rcases divisor_twenty_two_cases s hs with rfl | rfl | rfl | rfl
  all_goals norm_num at hlocal hglobal
  all_goals omega

end FiveTransitive.LongPrimeArithmetic

end CFSG
