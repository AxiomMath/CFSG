module

public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG.RankThree.Chevalley (exhaustionPhi)
open Polynomial

theorem prime_int_five : Prime (5 : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.1 (by norm_num : Nat.Prime 5)

theorem prime_int_seven : Prime (7 : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.1 (by norm_num : Nat.Prime 7)

theorem dvd_sub_one_of_dvd_phi_five {Q : ℤ} (h : (5 : ℤ) ∣ (exhaustionPhi 5).eval Q) :
    (5 : ℤ) ∣ Q - 1 := by
  have e : (exhaustionPhi 5).eval Q = (Q - 1) ^ 4 + 5 * (Q * (Q ^ 2 - Q + 1)) := by
    simp only [exhaustionPhi, eval_add, eval_pow, eval_X, eval_one]
    ring
  rw [e] at h
  exact prime_int_five.dvd_of_dvd_pow ((dvd_add_left (Dvd.intro _ rfl)).1 h)

theorem dvd_add_one_of_dvd_phi_ten {Q : ℤ} (h : (5 : ℤ) ∣ (exhaustionPhi 10).eval Q) :
    (5 : ℤ) ∣ Q + 1 := by
  have e : (exhaustionPhi 10).eval Q = (Q + 1) ^ 4 - 5 * (Q * (Q ^ 2 + Q + 1)) := by
    simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]
    ring
  rw [e] at h
  exact prime_int_five.dvd_of_dvd_pow ((dvd_sub_left (Dvd.intro _ rfl)).1 h)

theorem dvd_sub_one_of_dvd_phi_seven {Q : ℤ} (h : (7 : ℤ) ∣ (exhaustionPhi 7).eval Q) :
    (7 : ℤ) ∣ Q - 1 := by
  have e : (exhaustionPhi 7).eval Q = (Q - 1) ^ 6 + 7 * (Q * (Q ^ 2 - Q + 1) ^ 2) := by
    simp only [exhaustionPhi, eval_add, eval_pow, eval_X, eval_one]
    ring
  rw [e] at h
  exact prime_int_seven.dvd_of_dvd_pow ((dvd_add_left (Dvd.intro _ rfl)).1 h)

theorem dvd_add_one_of_dvd_phi_fourteen {Q : ℤ} (h : (7 : ℤ) ∣ (exhaustionPhi 14).eval Q) :
    (7 : ℤ) ∣ Q + 1 := by
  have e : (exhaustionPhi 14).eval Q = (Q + 1) ^ 6 - 7 * (Q * (Q ^ 2 + Q + 1) ^ 2) := by
    simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one]
    ring
  rw [e] at h
  exact prime_int_seven.dvd_of_dvd_pow ((dvd_sub_left (Dvd.intro _ rfl)).1 h)

theorem dvd_sub_one_of_dvd_phi_seven_of_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≤ 7)
    {Q : ℤ} (h : (p : ℤ) ∣ (exhaustionPhi 7).eval Q) : (p : ℤ) ∣ Q - 1 := by
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr rfl
  rcases hp57 with rfl | rfl
  · exfalso
    have key : ∀ r : ZMod 5, r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 ≠ 0 := by decide
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (by simpa using h)
    simp only [exhaustionPhi, eval_add, eval_pow, eval_X, eval_one] at h0
    push_cast at h0
    exact key _ h0
  · exact dvd_sub_one_of_dvd_phi_seven (by simpa using h)

theorem dvd_add_one_of_dvd_phi_fourteen_of_le {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≤ 7)
    {Q : ℤ} (h : (p : ℤ) ∣ (exhaustionPhi 14).eval Q) : (p : ℤ) ∣ Q + 1 := by
  have hp57 : p = 5 ∨ p = 7 := by
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr rfl
  rcases hp57 with rfl | rfl
  · exfalso
    have key : ∀ r : ZMod 5, r ^ 6 - r ^ 5 + r ^ 4 - r ^ 3 + r ^ 2 - r + 1 ≠ 0 := by decide
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (by simpa using h)
    simp only [exhaustionPhi, eval_add, eval_sub, eval_pow, eval_X, eval_one] at h0
    push_cast at h0
    exact key _ h0
  · exact dvd_add_one_of_dvd_phi_fourteen (by simpa using h)

end CFSG.RankThree.PartOne.KLC
