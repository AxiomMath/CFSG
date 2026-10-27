module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Tactic.NormNum.Basic

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

structure CentreSystem (k : Type) [Field k] where
  P : k → k → Prop
  add : ∀ {b c b' c' : k}, P b c → P b' c' → P (b + b') (c + c')
  zero : ∀ {c : k}, P 0 c → c = 0
  trans : ∀ {b c b' c' : k}, P b c → P b' c' → b ≠ 0 → b' ≠ 0 →
    ∃ l m : k, b' = l * b ∧ c' = m * c ∧ ∀ {β γ : k}, P β γ → P (l * β) (m * γ)
  b₀ : k
  c₀ : k
  base : P b₀ c₀
  b₀_ne : b₀ ≠ 0
  c₀_ne : c₀ ≠ 0

namespace CentreSystem

variable {k : Type} [Field k] [CharP k 2] (S : CentreSystem k)

theorem zero_zero : S.P 0 0 := by
  have h := S.add S.base S.base
  rwa [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero] at h

theorem eq_of_P {b c c' : k} (h : S.P b c) (h' : S.P b c') : c = c' := by
  have h2 := S.add h h'
  rw [CharTwo.add_self_eq_zero] at h2
  exact sub_eq_zero.mp (by rw [CharTwo.sub_eq_add]; exact S.zero h2)

@[expose] def F0 : Subfield k where
  carrier := {l | ∃ c, S.P (l * S.b₀) c}
  zero_mem' := ⟨0, by rw [zero_mul]; exact S.zero_zero⟩
  add_mem' := by
    rintro l l' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [add_mul]; exact S.add hc hc'⟩
  neg_mem' := by
    rintro l ⟨c, hc⟩
    exact ⟨c, by rwa [CharTwo.neg_eq]⟩
  one_mem' := ⟨S.c₀, by rw [one_mul]; exact S.base⟩
  mul_mem' := by
    rintro l l' ⟨c, hc⟩ ⟨c', hc'⟩
    by_cases hl : l = 0
    · exact ⟨0, by rw [hl, zero_mul, zero_mul]; exact S.zero_zero⟩
    · obtain ⟨t, m, ht, -, hall⟩ := S.trans S.base hc S.b₀_ne (mul_ne_zero hl S.b₀_ne)
      obtain rfl : t = l := (mul_right_cancel₀ S.b₀_ne ht).symm
      exact ⟨m * c', by rw [mul_assoc]; exact hall hc'⟩
  inv_mem' := by
    rintro l ⟨c, hc⟩
    by_cases hl : l = 0
    · exact ⟨0, by rw [hl, inv_zero, zero_mul]; exact S.zero_zero⟩
    · obtain ⟨t, m, ht, -, hall⟩ := S.trans hc S.base (mul_ne_zero hl S.b₀_ne) S.b₀_ne
      have htl : t = l⁻¹ := eq_inv_of_mul_eq_one_left
        (mul_right_cancel₀ S.b₀_ne (by rw [mul_assoc, ← ht, one_mul]))
      exact ⟨m * S.c₀, by rw [← htl]; exact hall S.base⟩

open Classical in
noncomputable def cval (l : k) : k :=
  if h : ∃ c, S.P (l * S.b₀) c then h.choose else 0

theorem P_cval {l : k} (hl : l ∈ S.F0) : S.P (l * S.b₀) (S.cval l) := by
  have hl' : ∃ c, S.P (l * S.b₀) c := hl
  simp only [cval, hl', dite_true]
  exact hl'.choose_spec

theorem cval_eq {l c : k} (h : S.P (l * S.b₀) c) : S.cval l = c :=
  S.eq_of_P (S.P_cval ⟨c, h⟩) h

noncomputable def chi (l : k) : k :=
  S.cval l / S.c₀

theorem div_mem_F0 {b c : k} (h : S.P b c) : b / S.b₀ ∈ S.F0 :=
  ⟨c, by rwa [div_mul_cancel₀ _ S.b₀_ne]⟩

theorem eq_chi {b c : k} (h : S.P b c) : c = S.c₀ * S.chi (b / S.b₀) := by
  rw [chi, mul_div_cancel₀ _ S.c₀_ne, S.cval_eq (by rwa [div_mul_cancel₀ _ S.b₀_ne])]

theorem chi_zero : S.chi 0 = 0 := by
  rw [chi, S.cval_eq (by rw [zero_mul]; exact S.zero_zero), zero_div]

theorem chi_one : S.chi 1 = 1 := by
  rw [chi, S.cval_eq (by rw [one_mul]; exact S.base), div_self S.c₀_ne]

theorem chi_add {l l' : k} (hl : l ∈ S.F0) (hl' : l' ∈ S.F0) :
    S.chi (l + l') = S.chi l + S.chi l' := by
  have h := S.add (S.P_cval hl) (S.P_cval hl')
  rw [← add_mul] at h
  rw [chi, chi, chi, S.cval_eq h, add_div]

theorem chi_mul {l l' : k} (hl : l ∈ S.F0) (hl' : l' ∈ S.F0) :
    S.chi (l * l') = S.chi l * S.chi l' := by
  by_cases h0 : l = 0
  · rw [h0, zero_mul, S.chi_zero, zero_mul]
  obtain ⟨t, m, ht, hm, hall⟩ :=
    S.trans S.base (S.P_cval hl) S.b₀_ne (mul_ne_zero h0 S.b₀_ne)
  obtain rfl : t = l := (mul_right_cancel₀ S.b₀_ne ht).symm
  have h := hall (S.P_cval hl')
  rw [← mul_assoc] at h
  rw [chi, chi, chi, S.cval_eq h, hm, mul_div_cancel_right₀ _ S.c₀_ne, mul_div_assoc]

theorem chi_pow {l : k} (hl : l ∈ S.F0) (n : ℕ) : S.chi (l ^ n) = S.chi l ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, S.chi_one]
  | succ n ih => rw [pow_succ, pow_succ, S.chi_mul (S.F0.pow_mem hl n) hl, ih]

theorem chi_inv {l : k} (hl : l ∈ S.F0) : S.chi l⁻¹ = (S.chi l)⁻¹ := by
  by_cases h0 : l = 0
  · rw [h0, inv_zero, S.chi_zero, inv_zero]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← S.chi_mul hl (S.F0.inv_mem hl), mul_inv_cancel₀ h0, S.chi_one]

theorem chi_ne_zero {l : k} (hl : l ∈ S.F0) (h0 : l ≠ 0) : S.chi l ≠ 0 := by
  intro h
  have := S.chi_mul hl (S.F0.inv_mem hl)
  rw [mul_inv_cancel₀ h0, S.chi_one, h, zero_mul] at this
  exact one_ne_zero this

end CentreSystem

end CFSG.Quasithin.Ch3E213M.G41.CTwo
