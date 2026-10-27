module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Walter.Ree.Hopkins

open Polynomial

variable {k : Type} [Field k] [CharP k 3]

@[expose] def hopF (r : ℕ) (u : k) : k :=
  u ^ r + (u - 1) ^ r + (u + 1) ^ r + (u ^ 2 - u) ^ r + (u ^ 2 + u) ^ r + (u ^ 2 - 1) ^ r

theorem three_eq_zero : (3 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 3

omit [CharP k 3] in
theorem eq_of_cube_eq_self {u : k} (hu : u ^ 3 = u) : u = 0 ∨ u = 1 ∨ u = -1 := by
  have h : u * (u - 1) * (u + 1) = 0 := by linear_combination hu
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem hopF_GF3 {r : ℕ} (hr : Even r) (hr0 : 0 < r) {u : k} (hu : u ^ 3 = u) :
    hopF r u = 0 := by
  have h3 := three_eq_zero (k := k)
  have hm1 : (-1 : k) ^ r = 1 := hr.neg_one_pow
  have hm2 : (-2 : k) ^ r = 1 := by
    rw [show (-2 : k) = 1 by linear_combination -h3, one_pow]
  have h2 : (2 : k) ^ r = 1 := by
    rw [show (2 : k) = -1 by linear_combination h3, hm1]
  rcases eq_of_cube_eq_self hu with rfl | rfl | rfl
  · simp only [hopF, zero_pow hr0.ne', zero_sub, zero_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, sub_zero, hm1, one_pow, add_zero]
    linear_combination h3
  · simp only [hopF, one_pow, sub_self, zero_pow hr0.ne', one_add_one_eq_two, h2]
    linear_combination h3
  · simp only [hopF, hm1, even_two, Even.neg_pow, one_pow, sub_self, zero_pow hr0.ne']
    rw [show (-1 : k) - 1 = -2 by ring, show (-1 : k) + 1 = 0 by ring,
      show (1 : k) - -1 = 2 by ring, show (1 : k) + -1 = 0 by ring, hm2, h2, zero_pow hr0.ne']
    linear_combination h3

variable [Fintype k]

omit [CharP k 3] in
theorem pow_compl {r : ℕ} (hr : r ≤ Fintype.card k - 1) {x : k} (hx : x ≠ 0) :
    x ^ (Fintype.card k - 1 - r) = (x ^ r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel hr, FiniteField.pow_card_sub_one_eq_one x hx]

theorem hopF_compl {m r : ℕ} (hk : Fintype.card k = 3 ^ m) (hr : Even r) (hr0 : 0 < r)
    (hrq : r < Fintype.card k - 1) (h : ∀ u : k, hopF r u = 0) :
    ∀ u : k, hopF (Fintype.card k - 1 - r) u = 0 := by
  intro u
  by_cases hu : u ^ 3 = u
  · refine hopF_GF3 ?_ (by omega) hu
    have hq : Odd (Fintype.card k) := by rw [hk]; exact Odd.pow (by decide)
    obtain ⟨c, hc⟩ := hq
    obtain ⟨e, he⟩ := hr
    exact ⟨c - e, by omega⟩
  · have hu' : u ≠ 0 ∧ u - 1 ≠ 0 ∧ u + 1 ≠ 0 := by
      refine ⟨?_, ?_, ?_⟩
      · rintro rfl; exact hu (by ring)
      · intro h1; exact hu (by rw [sub_eq_zero.mp h1]; ring)
      · intro h1; exact hu (by rw [eq_neg_of_add_eq_zero_left h1]; ring)
    obtain ⟨h0, h1, h2⟩ := hu'
    have hle : r ≤ Fintype.card k - 1 := hrq.le
    have e1 : u ^ 2 - u = u * (u - 1) := by ring
    have e2 : u ^ 2 + u = u * (u + 1) := by ring
    have e3 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
    have hF := h u
    simp only [hopF, e1, e2, e3, mul_pow] at hF ⊢
    rw [pow_compl hle h0, pow_compl hle h1, pow_compl hle h2]
    have hA := pow_ne_zero r h0
    have hB := pow_ne_zero r h1
    have hC := pow_ne_zero r h2
    field_simp
    linear_combination hF

omit [Fintype k] in
@[expose] noncomputable def hopPoly (r : ℕ) : k[X] :=
  X ^ r + (X + C (-1)) ^ r + (X + C 1) ^ r + X ^ r * (X + C (-1)) ^ r + X ^ r * (X + C 1) ^ r +
    expand k 2 ((X + C (-1)) ^ r)

omit [Fintype k] [CharP k 3] in
theorem eval_hopPoly (r : ℕ) (u : k) : (hopPoly r).eval u = hopF r u := by
  simp only [hopPoly, hopF, eval_add, eval_mul, eval_pow, eval_X, eval_C, expand_eval,
    show u ^ 2 - u = u * (u - 1) by ring, show u ^ 2 + u = u * (u + 1) by ring, mul_pow]
  ring

omit [Fintype k] [CharP k 3] in
theorem coeff_hopPoly (r n : ℕ) : (hopPoly r).coeff n =
    (if n = r then 1 else 0) + (-1) ^ (r - n) * (r.choose n : k) + (r.choose n : k) +
      (if r ≤ n then (-1) ^ (r - (n - r)) * (r.choose (n - r) : k) else 0) +
      (if r ≤ n then (r.choose (n - r) : k) else 0) +
      (if 2 ∣ n then (-1) ^ (r - n / 2) * (r.choose (n / 2) : k) else 0) := by
  simp only [hopPoly, coeff_add, coeff_X_pow, coeff_X_add_C_pow, coeff_X_pow_mul',
    coeff_expand (by norm_num : 0 < 2), one_pow, one_mul]

omit [Fintype k] in
theorem choose_two_cast {r : ℕ} (hr3 : r % 3 = 1) : (r.choose 2 : k) = 0 := by
  have h3 : 3 ∣ r.choose 2 := by
    have e : 2 * r.choose 2 = r * (r - 1) := by
      rw [Nat.choose_two_right]
      have : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
      omega
    have h1 : 3 ∣ r * (r - 1) := Dvd.dvd.mul_left (by omega) r
    rw [← e] at h1
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h1)
  obtain ⟨c, hc⟩ := h3
  rw [hc, Nat.cast_mul, show ((3 : ℕ) : k) = 3 by norm_num, three_eq_zero, zero_mul]

omit [Fintype k] in
theorem hopPoly_props {r : ℕ} (hr3 : r % 3 = 1) (hr4 : 4 ≤ r) :
    (hopPoly (k := k) r).natDegree ≤ 2 * r - 2 ∧ (hopPoly (k := k) r).coeff (2 * r - 2) = -1 := by
  have h3 := three_eq_zero (k := k)
  have hr1 : (r : k) = 1 := by
    have : r = 3 * (r / 3) + 1 := by omega
    rw [this]; push_cast; rw [h3]; ring
  refine ⟨?_, ?_⟩
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_hopPoly]
    have hnr : n ≠ r := by omega
    have hc1 : r.choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rcases (show n = 2 * r - 1 ∨ n = 2 * r ∨ 2 * r < n by omega) with rfl | rfl | hlt
    · have e1 : 2 * r - 1 - r = r - 1 := by omega
      have e2 : r - (r - 1) = 1 := by omega
      have e3 : ¬ 2 ∣ 2 * r - 1 := by omega
      rw [ite_eq_right hnr, hc1, ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right e3,
        e1, e2, Nat.choose_symm_of_eq_add (by omega : r = (r - 1) + 1), Nat.choose_one_right, hr1]
      simp
    · have e1 : 2 * r - r = r := by omega
      have e3 : 2 ∣ 2 * r := dvd_mul_right 2 r
      rw [ite_eq_right hnr, hc1, ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left e3, e1,
        Nat.mul_div_cancel_left r (by norm_num), Nat.sub_self, Nat.choose_self]
      simp; linear_combination h3
    · have hc2 : r.choose (n - r) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [ite_eq_right hnr, hc1, hc2]
      by_cases h2 : 2 ∣ n
      · have hc3 : r.choose (n / 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [ite_eq_left h2, hc3]
        simp
      · rw [ite_eq_right h2]
        simp
  · rw [coeff_hopPoly]
    have hnr : 2 * r - 2 ≠ r := by omega
    have hc1 : r.choose (2 * r - 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have e1 : 2 * r - 2 - r = r - 2 := by omega
    have e2 : r - (r - 2) = 2 := by omega
    have e3 : 2 ∣ 2 * r - 2 := ⟨r - 1, by omega⟩
    have e4 : (2 * r - 2) / 2 = r - 1 := by omega
    have e5 : r - (r - 1) = 1 := by omega
    rw [ite_eq_right hnr, hc1, ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left e3, e1,
      e2, e4, e5, Nat.choose_symm_of_eq_add (by omega : r = (r - 2) + 2),
      Nat.choose_symm_of_eq_add (by omega : r = (r - 1) + 1), Nat.choose_one_right, hr1,
      choose_two_cast hr3]
    simp

theorem exists_hopF_ne_zero {m r : ℕ} (hk : Fintype.card k = 3 ^ m) (hr : Even r)
    (hr3 : r % 3 = 1) (hr0 : 0 < r) (hrq : r < Fintype.card k - 1) : ∃ u : k, hopF r u ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  set q := Fintype.card k with hqdef
  have hq3 : q % 3 = 0 := by
    have hm : m ≠ 0 := by
      rintro rfl
      have := Fintype.one_lt_card (α := k); rw [← hqdef, hk] at this; simp at this
    rw [hk]; obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [pow_succ]; simp
  obtain ⟨r', hr'e, hr'3, hr'0, hr'q, hr'F⟩ : ∃ r', Even r' ∧ r' % 3 = 1 ∧ 0 < r' ∧
      2 * r' ≤ q - 1 ∧ ∀ u : k, hopF r' u = 0 := by
    by_cases hle : 2 * r ≤ q - 1
    · exact ⟨r, hr, hr3, hr0, hle, hcon⟩
    · refine ⟨q - 1 - r, ?_, by omega, by omega, by omega, hopF_compl hk hr hr0 hrq hcon⟩
      have hqo : Odd q := by rw [hk]; exact Odd.pow (by decide)
      obtain ⟨c, hc⟩ := hqo
      obtain ⟨e, he⟩ := hr
      exact ⟨c - e, by omega⟩
  have hr'4 : 4 ≤ r' := by
    obtain ⟨e, he⟩ := hr'e
    omega
  obtain ⟨hdeg, hcoeff⟩ := hopPoly_props (k := k) hr'3 hr'4
  have hzero : hopPoly (k := k) r' = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := id) Function.injective_id
    · intro u; rw [id, eval_hopPoly]; exact hr'F u
    · rw [Fintype.card_eq_nat_card, Nat.card_eq_fintype_card, ← hqdef]; omega
  rw [hzero, coeff_zero] at hcoeff
  have : (1 : k) = 0 := by linear_combination hcoeff
  exact one_ne_zero this

end CFSG.Walter.Ree.Hopkins
