module

public import Mathlib.Tactic.Group
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.Quasithin.H13.U43

variable {K : Type} [Group K]

theorem u43_cyc3 {a b y : K} (hab : a * b = b * a) (hab1 : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hya : y * a * y⁻¹ = 1 ∨ y * a * y⁻¹ = a ∨ y * a * y⁻¹ = b ∨ y * a * y⁻¹ = a * b)
    (hyb : y * b * y⁻¹ = 1 ∨ y * b * y⁻¹ = a ∨ y * b * y⁻¹ = b ∨ y * b * y⁻¹ = a * b)
    (hC : ∀ x : K, x * a = a * x → x ^ 3 = 1 → x = 1) (haa : a * a = 1) (hbb : b * b = 1)
    (hmove : ¬ (y * a = a * y)) :
    ∃ ν : K, (ν = y ∨ ν = y⁻¹) ∧ ν * a = b * ν ∧ ν * b = (a * b) * ν := by
  have hy3' : y * y * y = 1 := by
    rw [← pow_three']
    exact hy3
  have hsq : y * (y * a * y⁻¹) * y⁻¹ = a → False := by
    intro h
    have h1 : (y * y) * a = a * (y * y) := by
      have : (y * y) * a * (y * y)⁻¹ = a := by
        calc (y * y) * a * (y * y)⁻¹ = y * (y * a * y⁻¹) * y⁻¹ := by group
          _ = a := h
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h2 : y * y = 1 := by
      apply hC (y * y) h1
      rw [pow_three']
      calc y * y * (y * y) * (y * y) = (y * y * y) * (y * y * y) := by group
        _ = 1 := by rw [hy3', one_mul]
    apply hy1
    calc y = (y * y * y) * (y * y)⁻¹ := by group
      _ = 1 := by rw [hy3', h2]; group
  have hne1 : y * a * y⁻¹ ≠ 1 := by
    intro h
    apply ha1
    rw [mul_inv_eq_one] at h
    exact mul_left_cancel (h.trans (mul_one y).symm)
  have hne2 : y * b * y⁻¹ ≠ 1 := by
    intro h
    apply hb1
    rw [mul_inv_eq_one] at h
    exact mul_left_cancel (h.trans (mul_one y).symm)
  have hnea : y * a * y⁻¹ ≠ a := fun h => hmove (by rw [mul_inv_eq_iff_eq_mul] at h; exact h)
  have hdist : y * a * y⁻¹ ≠ y * b * y⁻¹ := by
    intro h
    apply hab1
    have := mul_right_cancel h
    exact mul_left_cancel this
  have hcomb : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
  rcases hya with h | h | h | h
  · exact absurd h hne1
  · exact absurd h hnea
  ·
    rcases hyb with h' | h' | h' | h'
    · exact absurd h' hne2
    · exfalso
      exact hsq (by rw [h, h'])
    · exact absurd (h'.trans h.symm) hdist.symm
    · refine ⟨y, Or.inl rfl, ?_, ?_⟩
      · rw [mul_inv_eq_iff_eq_mul] at h
        exact h
      · rw [mul_inv_eq_iff_eq_mul] at h'
        exact h'
  ·
    rcases hyb with h' | h' | h' | h'
    · exact absurd h' hne2
    · refine ⟨y⁻¹, Or.inr rfl, ?_, ?_⟩
      ·
        have e : y⁻¹ * a * y = b := by
          calc y⁻¹ * a * y = y⁻¹ * (y * b * y⁻¹) * y := by rw [h']
            _ = b := by group
        rw [← e]
        group
      ·
        have e1 : y * (a * b) * y⁻¹ = b := by
          rw [hcomb, h, h']
          calc a * b * a = a * (b * a) := by group
            _ = a * (a * b) := by rw [hab]
            _ = (a * a) * b := by group
            _ = b := by rw [haa, one_mul]
        have e : y⁻¹ * b * y = a * b := by
          calc y⁻¹ * b * y = y⁻¹ * (y * (a * b) * y⁻¹) * y := by rw [e1]
            _ = a * b := by group
        rw [← e]
        group
    · exfalso
      have e1 : y * (a * b) * y⁻¹ = a := by
        rw [hcomb, h, h']
        calc a * b * b = a * (b * b) := by group
          _ = a := by rw [hbb, mul_one]
      have : y * (y * a * y⁻¹) * y⁻¹ = a := by
        rw [h]
        exact e1
      exact hsq this
    · exact absurd (h'.trans h.symm) hdist.symm

end CFSG.Quasithin.H13.U43
