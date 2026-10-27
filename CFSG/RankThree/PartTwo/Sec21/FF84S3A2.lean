module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3A1
import CFSG.RankThree.PartTwo.Sec21.FF84S3A2K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

set_option maxRecDepth 200000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem C_m1_facts : ∀ σ : P8, σ * m₁ = m₁ * σ →
    (σ * m₂ * σ⁻¹ = m₂ ∨ σ * m₂ * σ⁻¹ = m₂⁻¹) ∧
    (σ ^ 3 = 1 → σ ≠ 1 → σ ≠ m₁ → σ ≠ m₁ ^ 2 →
      (σ = m₂ ∨ σ = m₂⁻¹ ∨ σ = m₁ * m₂ ∨ σ = (m₁ * m₂)⁻¹ ∨ σ = m₁ * m₂ ^ 2 ∨
        σ = (m₁ * m₂ ^ 2)⁻¹)) ∧
    (σ * σ = 1 → σ ≠ 1 → Equiv.Perm.sign σ = 1 →
      (σ * (m₂ * σ * m₂⁻¹)) ^ 3 = 1 ∧ σ * (m₂ * σ * m₂⁻¹) ≠ 1) ∧
    (σ * m₂ = m₂ * σ → ∃ i : ℕ, i < 3 ∧ ∃ j : ℕ, j < 3 ∧ ∃ k : ℕ, k < 2 ∧
      σ = m₁ ^ i * m₂ ^ j * τ₀ ^ k) := by
  intro σ hσ
  exact S3A2K.facts σ hσ

theorem A3_small (i j k : ℕ) (hi : i < 3) (hj : j < 3) (hk : k < 2) :
    (m₁ ^ i * m₂ ^ j * τ₀ ^ k) * (m₁ ^ i * m₂ ^ j * τ₀ ^ k) = 1 →
      m₁ ^ i * m₂ ^ j * τ₀ ^ k = 1 ∨ m₁ ^ i * m₂ ^ j * τ₀ ^ k = τ₀ := by
  interval_cases i <;> interval_cases j <;> interval_cases k <;> decide +kernel

theorem m₁_cube : m₁ ^ 3 = 1 := by decide +kernel

theorem m₂_cube : m₂ ^ 3 = 1 := by decide +kernel

theorem cycleType_m1m2 : (m₁ * m₂).cycleType = {3} := by
  have e : m₁ * m₂ = (List.formPerm [0, 2, 1] : P8) := by decide +kernel
  have h3 : (List.formPerm [0, 2, 1] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  rw [e]
  exact h3.cycleType

theorem cycleType_m1m2sq : (m₁ * m₂ ^ 2).cycleType = {3} := by
  have e : m₁ * m₂ ^ 2 = (List.formPerm [3, 5, 4] : P8) := by decide +kernel
  have h3 : (List.formPerm [3, 5, 4] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  rw [e]
  exact h3.cycleType

theorem A3_centralizer_Eo (σ : P8) (h₁ : σ * m₁ = m₁ * σ) (h₂ : σ * m₂ = m₂ * σ) :
    ∃ i j k : ℕ, k < 2 ∧ σ = m₁ ^ i * m₂ ^ j * τ₀ ^ k := by
  obtain ⟨i, _, j, _, k, hk, heq⟩ := (C_m1_facts σ h₁).2.2.2 h₂
  exact ⟨i, j, k, hk, heq⟩

theorem A3_inv (σ : P8) (h₁ : σ * m₁ = m₁ * σ) (h₂ : σ * m₂ = m₂ * σ) (h : σ * σ = 1) :
    σ = 1 ∨ σ = τ₀ := by
  obtain ⟨i, j, k, hk, rfl⟩ := A3_centralizer_Eo σ h₁ h₂
  have e1 : m₁ ^ i = m₁ ^ (i % 3) := pow_eq_pow_mod i m₁_cube
  have e2 : m₂ ^ j = m₂ ^ (j % 3) := pow_eq_pow_mod j m₂_cube
  rw [e1, e2] at h ⊢
  exact A3_small (i % 3) (j % 3) k (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hk h

theorem A4_centralizer_m₁ (σ : P8) (h : σ * m₁ = m₁ * σ) :
    σ * m₂ * σ⁻¹ = m₂ ∨ σ * m₂ * σ⁻¹ = m₂⁻¹ :=
  (C_m1_facts σ h).1

theorem conj_fix_m₁ (y : P8) (h : y = m₂ ∨ y = m₂⁻¹) :
    ∃ g : P8, g * m₁ * g⁻¹ = m₁ ∧ g * y * g⁻¹ = m₂ := by
  rcases h with rfl | rfl
  · exact ⟨1, by simp, by simp⟩
  · exact ⟨Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5, by decide, by decide⟩

theorem A2_normalize (x₁ x₂ : P8) (h₁ : x₁ ∈ A8s) (h₂ : x₂ ∈ A8s) (hc : x₁ * x₂ = x₂ * x₁)
    (o₁ : orderOf x₁ = 3) (o₂ : orderOf x₂ = 3) (t₁ : x₁.cycleType = {3, 3})
    (t₂ : x₂.cycleType = {3, 3}) (hn : x₂ ∉ Subgroup.zpowers x₁) :
    ∃ σ : P8, σ * x₁ * σ⁻¹ = m₁ ∧ σ * x₂ * σ⁻¹ = m₂ := by
  obtain ⟨σ₁, hσ₁⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (t₁.trans cycleType_m₁.symm))
  have hyc : (σ₁ * x₂ * σ₁⁻¹) * m₁ = m₁ * (σ₁ * x₂ * σ₁⁻¹) := by
    rw [← hσ₁]
    calc (σ₁ * x₂ * σ₁⁻¹) * (σ₁ * x₁ * σ₁⁻¹) = σ₁ * (x₂ * x₁) * σ₁⁻¹ := by group
      _ = σ₁ * (x₁ * x₂) * σ₁⁻¹ := by rw [hc]
      _ = (σ₁ * x₁ * σ₁⁻¹) * (σ₁ * x₂ * σ₁⁻¹) := by group
  have hx23 : x₂ ^ 3 = 1 := by rw [← o₂]; exact pow_orderOf_eq_one x₂
  have hy3 : (σ₁ * x₂ * σ₁⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx23, mul_one, mul_inv_cancel]
  have hyct : (σ₁ * x₂ * σ₁⁻¹).cycleType = {3, 3} := by
    rw [cycleType_conj]; exact t₂
  have hne1 : σ₁ * x₂ * σ₁⁻¹ ≠ 1 := by
    intro h
    rw [h, cycleType_one] at hyct
    exact absurd hyct (by decide)
  have hmem : ∀ n : ℕ, σ₁ * x₂ * σ₁⁻¹ = m₁ ^ n → False := by
    intro n hn'
    apply hn
    rw [← hσ₁, conj_pow] at hn'
    have hx : x₂ = x₁ ^ n := by
      have h' := mul_right_cancel hn'
      exact mul_left_cancel h'
    rw [hx]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) n
  have hne_m1 : σ₁ * x₂ * σ₁⁻¹ ≠ m₁ := fun h => hmem 1 (by rw [h, pow_one])
  have hne_m1sq : σ₁ * x₂ * σ₁⁻¹ ≠ m₁ ^ 2 := fun h => hmem 2 h
  have hy' : σ₁ * x₂ * σ₁⁻¹ = m₂ ∨ σ₁ * x₂ * σ₁⁻¹ = m₂⁻¹ := by
    rcases (C_m1_facts _ hyc).2.1 hy3 hne1 hne_m1 hne_m1sq with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, cycleType_m1m2] at hyct; exact absurd hyct (by decide)
    · rw [h, cycleType_inv, cycleType_m1m2] at hyct; exact absurd hyct (by decide)
    · rw [h, cycleType_m1m2sq] at hyct; exact absurd hyct (by decide)
    · rw [h, cycleType_inv, cycleType_m1m2sq] at hyct; exact absurd hyct (by decide)
  obtain ⟨g, hg1, hg2⟩ := conj_fix_m₁ _ hy'
  refine ⟨g * σ₁, ?_, ?_⟩
  · calc g * σ₁ * x₁ * (g * σ₁)⁻¹ = g * (σ₁ * x₁ * σ₁⁻¹) * g⁻¹ := by group
      _ = g * m₁ * g⁻¹ := by rw [hσ₁]
      _ = m₁ := hg1
  · calc g * σ₁ * x₂ * (g * σ₁)⁻¹ = g * (σ₁ * x₂ * σ₁⁻¹) * g⁻¹ := by group
      _ = m₂ := hg2

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
