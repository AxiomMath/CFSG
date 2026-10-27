module

public import CFSG.Quasithin.H13.A5Setting
import CFSG.Adapters.ProjectiveSpecialLinear

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

namespace CertificateChecks.Batch17038

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.LieType.BorelTits

private theorem InK4_mul_0 :  ∀ σ τ : Equiv.Perm (Fin 5), InK4 σ → InK4 τ → InK4 (σ * τ)  := by
  decide +kernel

private theorem InK4_inv_1 :  ∀ σ : Equiv.Perm (Fin 5), InK4 σ → InK4 σ⁻¹  := by
  decide +kernel

private theorem InK4_conj'_2 :  ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → σ.sign = 1 → InK4 τ →
    InK4 (σ * τ * σ⁻¹)  := by
  decide +kernel

private theorem InK4_sq_3 :  ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ * σ = 1  := by
  decide +kernel

private theorem A4_decomp'_4 :  ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ 4 = 4 →
    InK4 σ ∨ InK4 (c3p * c3p * σ) ∨ InK4 (c3p * σ)  := by
  decide +kernel

end CertificateChecks.Batch17038

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.LieType.BorelTits in
theorem certificate17038 : (
 ∀ σ τ : Equiv.Perm (Fin 5), InK4 σ → InK4 τ → InK4 (σ * τ) 
)
    ∧ (
 ∀ σ : Equiv.Perm (Fin 5), InK4 σ → InK4 σ⁻¹ 
)
    ∧ (
 ∀ σ τ : Equiv.Perm (Fin 5), σ 4 = 4 → σ.sign = 1 → InK4 τ →
    InK4 (σ * τ * σ⁻¹) 
)
    ∧ (
 ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ * σ = 1 
)
    ∧ (
 ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → σ 4 = 4 →
    InK4 σ ∨ InK4 (c3p * c3p * σ) ∨ InK4 (c3p * σ) 
) := by
  exact ⟨@CertificateChecks.Batch17038.InK4_mul_0, @CertificateChecks.Batch17038.InK4_inv_1, @CertificateChecks.Batch17038.InK4_conj'_2, @CertificateChecks.Batch17038.InK4_sq_3, @CertificateChecks.Batch17038.A4_decomp'_4⟩

end Certificates
