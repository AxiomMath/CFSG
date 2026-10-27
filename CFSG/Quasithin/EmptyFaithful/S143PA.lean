module

public import Certificates.Certificate17013
public import CFSG.Adapters.ProjectiveSpecialLinear


public section

namespace CFSG.Quasithin.S143

namespace A6Model

set_option maxRecDepth 100000 in
theorem n6Comm_not_transvection : ∀ σ : Equiv.Perm (Fin 6), σ.sign = 1 → σ ≠ 1 →
    ∃ b₁ b₂ : N6, n6Comm σ b₁ ≠ 1 ∧ n6Comm σ b₂ ≠ 1 ∧ n6Comm σ b₁ ≠ n6Comm σ b₂ :=
  Certificates.certificate17013.1

set_option maxRecDepth 100000 in
theorem swap_comm_cases' : ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q →
    σ * Equiv.swap p q = Equiv.swap p q * σ → (σ p = p ∧ σ q = q) ∨ (σ p = q ∧ σ q = p) :=
  Certificates.certificate17013.2.1

set_option maxRecDepth 100000 in
theorem even_invol_swap : ∀ (p q : Fin 6) (σ : Equiv.Perm (Fin 6)), p ≠ q → σ.sign = 1 →
    σ * σ = 1 → σ p = q → ∃ a b : Fin 6, a ≠ b ∧ Equiv.swap p q * σ = Equiv.swap a b :=
  Certificates.certificate17013.2.2.1

set_option maxRecDepth 100000 in
theorem exists_even_conj_swap : ∀ p q a b : Fin 6, p ≠ q → a ≠ b →
    ∃ τ : Equiv.Perm (Fin 6), τ.sign = 1 ∧ τ * Equiv.swap p q * τ⁻¹ = Equiv.swap a b :=
  Certificates.certificate17013.2.2.2

theorem perm_eq_of_n6Act_eq {σ σ' : Equiv.Perm (Fin 6)} (h : ∀ b : N6, n6Act σ b = n6Act σ' b) :
    σ = σ' := by
  have h1 : σ'⁻¹ * σ = 1 := by
    apply n6_faithful_perm
    intro b
    rw [map_mul, MulAut.mul_apply, h b, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact (inv_mul_eq_one.mp h1).symm

end A6Model

end CFSG.Quasithin.S143
