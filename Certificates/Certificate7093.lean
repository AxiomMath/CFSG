module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Inputs
import Certificates.Kernel.Direct.C7093

public section

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H13.A6Coc in
theorem certificate7093 : ∀ τ₁ τ₂ : Equiv.Perm (Fin 6), τ₁ ^ 3 = 1 ∧ fixCount τ₁ = 4 ∧ τ₂ ^ 5 = 1 ∧
      (τ₁ * τ₂) ^ 4 = 1 ∧ (τ₁ ^ 2 * τ₂ ^ 2) ^ 3 = 1 →
    ∃ σ : Equiv.Perm (Fin 6), σ * aP * σ⁻¹ = τ₁ ∧ σ * bP * σ⁻¹ = τ₂ :=
  fun τ₁ τ₂ h => KernelDirect.C7093.a6Aut_curried τ₁ ⟨h.1, h.2.1⟩ τ₂ h.2.2

end Certificates
