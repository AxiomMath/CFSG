module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Inputs
import Mathlib.Tactic.Group
public import Mathlib.Data.Fintype.Perm

public section

namespace CertificateChecks.KernelDirect.C7093

open CFSG.Quasithin.H13.A6Coc Equiv

def conjCands : List (Perm (Fin 6)) :=
  (List.finRange 6).flatMap fun a => (List.finRange 6).flatMap fun b =>
    (List.finRange 6).map fun c => swap 0 a * swap 1 b * swap 2 c

def centCands : List (Perm (Fin 6)) :=
  [1, aP, aP * aP].flatMap fun x =>
    [1, swap 3 4, swap 3 5, swap 4 5, swap 3 4 * swap 4 5, swap 4 5 * swap 3 4].map (x * ·)

set_option maxRecDepth 100000 in
theorem a6Aut_conjA : ∀ τ₁ : Perm (Fin 6), τ₁ ^ 3 = 1 ∧ fixCount τ₁ = 4 →
    ∃ g ∈ conjCands, g * aP * g⁻¹ = τ₁ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a6Aut_centB : ∀ τ₂ : Perm (Fin 6), τ₂ ^ 5 = 1 ∧ (aP * τ₂) ^ 4 = 1 ∧
    (aP ^ 2 * τ₂ ^ 2) ^ 3 = 1 → ∃ σ ∈ centCands, σ * aP * σ⁻¹ = aP ∧ σ * bP * σ⁻¹ = τ₂ := by
  decide +kernel

theorem a6Aut_curried : ∀ τ₁ : Equiv.Perm (Fin 6), τ₁ ^ 3 = 1 ∧ fixCount τ₁ = 4 →
    ∀ τ₂ : Equiv.Perm (Fin 6), τ₂ ^ 5 = 1 ∧ (τ₁ * τ₂) ^ 4 = 1 ∧ (τ₁ ^ 2 * τ₂ ^ 2) ^ 3 = 1 →
      ∃ σ : Equiv.Perm (Fin 6), σ * aP * σ⁻¹ = τ₁ ∧ σ * bP * σ⁻¹ = τ₂ := by
  intro τ₁ h₁ τ₂ h₂
  obtain ⟨g, -, rfl⟩ := a6Aut_conjA τ₁ h₁
  have hT : τ₂ = g * (g⁻¹ * τ₂ * g) * g⁻¹ := by group
  obtain ⟨h5, h4, h3⟩ := h₂
  obtain ⟨σ, -, hσ1, hσ2⟩ := a6Aut_centB (g⁻¹ * τ₂ * g) ⟨by
      rw [← conj_eq_one_iff (a := g), ← conj_pow, ← hT]; exact h5, by
      rw [← conj_eq_one_iff (a := g), ← conj_pow]
      have e : g * (aP * (g⁻¹ * τ₂ * g)) * g⁻¹ = g * aP * g⁻¹ * τ₂ := by group
      rw [e]; exact h4, by
      rw [← conj_eq_one_iff (a := g), ← conj_pow]
      have e : g * (aP ^ 2 * (g⁻¹ * τ₂ * g) ^ 2) * g⁻¹ = (g * aP * g⁻¹) ^ 2 * τ₂ ^ 2 := by
        simp only [pow_two]; group
      rw [e]; exact h3⟩
  refine ⟨g * σ, ?_, ?_⟩
  · calc g * σ * aP * (g * σ)⁻¹ = g * (σ * aP * σ⁻¹) * g⁻¹ := by group
      _ = g * aP * g⁻¹ := by rw [hσ1]
  · calc g * σ * bP * (g * σ)⁻¹ = g * (σ * bP * σ⁻¹) * g⁻¹ := by group
      _ = τ₂ := by rw [hσ2]; group

end CertificateChecks.KernelDirect.C7093
