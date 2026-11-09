module

public import CFSG.Quasithin.EmptyFaithful.S143PAInputs
import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

namespace CertificateChecks.Batch17013

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model

set_option maxRecDepth 100000 in
private theorem n6Comm_not_transvection_0 :  ∀ σ : Equiv.Perm (Fin 6), σ.sign = 1 → σ ≠ 1 →
    ∃ b₁ b₂ : N6, n6Comm σ b₁ ≠ 1 ∧ n6Comm σ b₂ ≠ 1 ∧ n6Comm σ b₁ ≠ n6Comm σ b₂  := by
  decide +kernel

private theorem swap_comm_cases'_1 :  ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q →
    σ * Equiv.swap p q = Equiv.swap p q * σ → (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p)  := by
  intro p q σ hpq h
  have hp : σ q = Equiv.swap p q (σ p) := by
    have h' := DFunLike.congr_fun h p
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h'
  rcases eq_or_ne (σ p) p with h1 | h1
  · exact Or.inl ⟨h1, by rw [hp, h1, Equiv.swap_apply_left]⟩
  · rcases eq_or_ne (σ p) q with h2 | h2
    · exact Or.inr ⟨h2, by rw [hp, h2, Equiv.swap_apply_right]⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at hp
      exact absurd (σ.injective hp).symm hpq

set_option maxRecDepth 100000 in
private theorem even_invol_swap_2 :  ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q → σ.sign = 1 →
    σ * σ = 1 → σ p = q → ∃ a b : Fin 6, a ≠ b ∧ Equiv.swap p q * σ = Equiv.swap a b  := by
  decide +kernel

private theorem exists_even_conj_swap_3 :  ∀ p q a b : Fin 6, p ≠ q → a ≠ b →
    ∃ τ : Equiv.Perm (Fin 6), τ.sign = 1 ∧ τ * Equiv.swap p q * τ⁻¹ = Equiv.swap a b  := by
  intro p q a b hpq hab
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hpq hab)
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h
  · exact ⟨c, h, hc⟩
  · refine ⟨c * Equiv.swap p q, ?_, ?_⟩
    · simp [Equiv.Perm.sign_mul, h, Equiv.Perm.sign_swap hpq]
    · rw [← hc, ← Equiv.swap_apply_apply, ← Equiv.swap_apply_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_comm]

end CertificateChecks.Batch17013

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.S143 CFSG.Quasithin.S143.A6Model in
theorem certificate17013 : (
 ∀ σ : Equiv.Perm (Fin 6), σ.sign = 1 → σ ≠ 1 →
    ∃ b₁ b₂ : N6, n6Comm σ b₁ ≠ 1 ∧ n6Comm σ b₂ ≠ 1 ∧ n6Comm σ b₁ ≠ n6Comm σ b₂ 
)
    ∧ (
 ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q →
    σ * Equiv.swap p q = Equiv.swap p q * σ → (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p) 
)
    ∧ (
 ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q → σ.sign = 1 →
    σ * σ = 1 → σ p = q → ∃ a b : Fin 6, a ≠ b ∧ Equiv.swap p q * σ = Equiv.swap a b 
)
    ∧ (
 ∀ p q a b : Fin 6, p ≠ q → a ≠ b →
    ∃ τ : Equiv.Perm (Fin 6), τ.sign = 1 ∧ τ * Equiv.swap p q * τ⁻¹ = Equiv.swap a b 
) := by
  exact ⟨@CertificateChecks.Batch17013.n6Comm_not_transvection_0, @CertificateChecks.Batch17013.swap_comm_cases'_1, @CertificateChecks.Batch17013.even_invol_swap_2, @CertificateChecks.Batch17013.exists_even_conj_swap_3⟩

end Certificates
