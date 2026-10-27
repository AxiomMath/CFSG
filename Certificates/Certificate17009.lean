module

public import CFSG.Quasithin.Recognition.M12AscE2Inputs
public import CFSG.Quasithin.Recognition.M12AscL2

public section

open CFSG CFSG.Quasithin Subgroup Equiv

namespace CertificateChecks.Batch17009

open CFSG CFSG.Quasithin Subgroup Equiv

private theorem sign_pa_0 : Equiv.Perm.sign pa = 1 := by
  decide +kernel

private theorem sign_sig3_1 : Equiv.Perm.sign sig3 = 1 := by
  decide +kernel

private theorem pa_not_norm_2 : NormDb pa = false := by
  decide +kernel

private theorem sig3_not_norm_3 : NormDb sig3 = false := by
  decide +kernel

private theorem pa_sig3_not_norm_4 : NormDb (pa⁻¹ * sig3) = false := by
  decide +kernel

private theorem stab_D_5 : ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormDb τ = true →
    NormDb (pa⁻¹ * τ * pa) = true → NormDb (sig3⁻¹ * τ * sig3) = true → τ = 1 := by
  decide +kernel

private theorem stab_E_6 : ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormEb τ = true →
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true → NormEb (sig3⁻¹ * τ * (TA 3 * TA 2)) = true →
    False := by
  decide +kernel

private theorem card_H_D_7 : Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormDb τ = true ∧
    NormDb (pa⁻¹ * τ * pa) = true} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem card_H_E_8 : Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormEb τ = true ∧
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true} = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end CertificateChecks.Batch17009

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin Subgroup Equiv in
theorem certificate17009 : (
 Equiv.Perm.sign pa = 1 
)
    ∧ (
 Equiv.Perm.sign sig3 = 1 
)
    ∧ (
 NormDb pa = false 
)
    ∧ (
 NormDb sig3 = false 
)
    ∧ (
 NormDb (pa⁻¹ * sig3) = false 
)
    ∧ (
 ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormDb τ = true →
    NormDb (pa⁻¹ * τ * pa) = true → NormDb (sig3⁻¹ * τ * sig3) = true → τ = 1 
)
    ∧ (
 ∀ τ : Perm (Fin 6), Equiv.Perm.sign τ = 1 → NormEb τ = true →
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true → NormEb (sig3⁻¹ * τ * (TA 3 * TA 2)) = true →
    False 
)
    ∧ (
 Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormDb τ = true ∧
    NormDb (pa⁻¹ * τ * pa) = true} = 4 
)
    ∧ (
 Nat.card {τ : Perm (Fin 6) // Equiv.Perm.sign τ = 1 ∧ NormEb τ = true ∧
    NormEb (pa⁻¹ * τ * (TA 2 * TA 4)) = true} = 4 
) := by
  exact ⟨@CertificateChecks.Batch17009.sign_pa_0, @CertificateChecks.Batch17009.sign_sig3_1, @CertificateChecks.Batch17009.pa_not_norm_2, @CertificateChecks.Batch17009.sig3_not_norm_3, @CertificateChecks.Batch17009.pa_sig3_not_norm_4, @CertificateChecks.Batch17009.stab_D_5, @CertificateChecks.Batch17009.stab_E_6, @CertificateChecks.Batch17009.card_H_D_7, @CertificateChecks.Batch17009.card_H_E_8⟩

end Certificates
