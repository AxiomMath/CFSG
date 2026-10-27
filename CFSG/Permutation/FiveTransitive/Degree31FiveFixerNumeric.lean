module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveFixerNumeric

theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (hdiv : h ∣ 308403583488000)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3)
    (h9 : ¬ 9 ∣ h) :
    ∃ a ≤ 12, ∃ b ≤ 1, h = 2 ^ a * 3 ^ b := by
  let a := h.factorization 2
  let b := h.factorization 3
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 3 ^ b ∣ h := (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hale : a ≤ 12 := by
    by_contra hn
    have hd : 8192 ∣ h := (show 2^13 ∣ 2^a from pow_dvd_pow 2 (by omega)).trans ha
    have hc := hd.trans hdiv
    norm_num at hc
  have hble : b ≤ 1 := by
    by_contra hn
    exact h9 ((show 3^2 ∣ 3^b from pow_dvd_pow 3 (by omega)).trans hb)
  refine ⟨a,hale,b,hble,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num)))
  intro p
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
    Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow,
    Finsupp.smul_apply, Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a, Nat.prime_two.factorization, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
  by_cases hp3 : p = 3
  · subst p
    norm_num [b, (show Nat.Prime 3 by norm_num).factorization,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 hp3))
    · exact Or.inl hp
  simp [hz, Nat.prime_two.factorization, (show Nat.Prime 3 by norm_num).factorization,
    hp2, hp3]

private theorem twenty_nine_cases {a b d j : ℕ}
    (ha : a ≤ 12) (hb : b ≤ 1) (hd : d ∣ 28) (hdeven : 2 ∣ d)
    (hj : j % 29 = 1) (heq : d * j * 29 = 20389320 * 2 ^ a * 3 ^ b) :
    (a = 0 ∧ b = 0) ∨ (a = 6 ∧ b = 1) ∨ (a = 7 ∧ b = 1) ∨
      (a = 11 ∧ b = 0) ∨ (a = 12 ∧ b = 0) := by
  have hdle : d ≤ 28 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> norm_num at hd
  all_goals norm_num at hdeven
  all_goals interval_cases a <;> interval_cases b <;> norm_num at heq ⊢ <;> omega

theorem exponents_unique {a b d29 j29 d31 j31 : ℕ}
    (ha : a ≤ 12) (hb : b ≤ 1) (hd29 : d29 ∣ 28) (heven : 2 ∣ d29)
    (hj29 : j29 % 29 = 1) (heq29 : d29*j29*29 = 20389320*2^a*3^b)
    (hd31 : d31 ∣ 30) (hj31 : j31 % 31 = 1)
    (heq31 : d31*j31*31 = 20389320*2^a*3^b) : a = 12 ∧ b = 0 := by
  have hc := twenty_nine_cases ha hb hd29 heven hj29 heq29
  have hdle : d31 ≤ 30 := Nat.le_of_dvd (by norm_num) hd31
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals try { exact ⟨rfl,rfl⟩ }
  all_goals interval_cases d31 <;> norm_num at hd31
  all_goals norm_num at heq31 ⊢; omega

end FiveTransitive.Degree31FiveFixerNumeric

end CFSG
