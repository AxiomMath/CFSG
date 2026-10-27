module

public import CFSG.Quasithin.Recognition.M12AscD12
public import CFSG.Quasithin.Recognition.M12AscD13Inputs

public section

open CFSG CFSG.Quasithin Subgroup Equiv

namespace CertificateChecks.Batch17018

open CFSG CFSG.Quasithin Subgroup Equiv

private theorem W1_ok_0 :  ∀ σ ∈ W1, Equiv.Perm.sign σ = 1 ∧ NormDb σ = true  := by
  decide +kernel

private theorem W2_ok_1 :  ∀ σ ∈ W2, Equiv.Perm.sign σ = 1 ∧ NormEb σ = true  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_D_2 :  ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormDb σ = true → InKP (actD σ)  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_E_3 :  ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormEb σ = true → InKP (actE σ)  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_mem1_4 :  ∀ σ ∈ W1, (actD σ).1 ∈ D6l ∧ (actD σ).2 ∈ D6l ∧
    (actD σ).1 * ((actD σ).2 * (actD σ).2) ∈ D6l  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_mem2_5 :  ∀ σ ∈ W2, (actE σ).1 ∈ D6l ∧ (actE σ).2 ∈ D6l ∧
    (actE σ).1 * ((actE σ).2 * (actE σ).2) ∈ D6l  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_conj1_6 :  ∀ σ ∈ W1,
    InKP (fAct x6 bv (actD σ).1, fAct x6 bv ((actD σ).1 * ((actD σ).2 * (actD σ).2)))  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_conj2_7 :  ∀ σ ∈ W2,
    InKP (fAct x6 bv (actE σ).1, fAct x6 bv ((actE σ).1 * ((actE σ).2 * (actE σ).2)))  := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem KP_not_v_8 :  ¬ InKP (x6, bv)  := by
  decide +kernel

private theorem D6_sign_norm_9 :  ∀ d ∈ D6l, Equiv.Perm.sign d = 1 ∧ NormDb d = true  := by
  decide +kernel

end CertificateChecks.Batch17018

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin Subgroup Equiv in
theorem certificate17018 : (
 ∀ σ ∈ W1, Equiv.Perm.sign σ = 1 ∧ NormDb σ = true 
)
    ∧ (
 ∀ σ ∈ W2, Equiv.Perm.sign σ = 1 ∧ NormEb σ = true 
)
    ∧ (
 ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormDb σ = true → InKP (actD σ) 
)
    ∧ (
 ∀ σ : Perm (Fin 6), Equiv.Perm.sign σ = 1 → NormEb σ = true → InKP (actE σ) 
)
    ∧ (
 ∀ σ ∈ W1, (actD σ).1 ∈ D6l ∧ (actD σ).2 ∈ D6l ∧
    (actD σ).1 * ((actD σ).2 * (actD σ).2) ∈ D6l 
)
    ∧ (
 ∀ σ ∈ W2, (actE σ).1 ∈ D6l ∧ (actE σ).2 ∈ D6l ∧
    (actE σ).1 * ((actE σ).2 * (actE σ).2) ∈ D6l 
)
    ∧ (
 ∀ σ ∈ W1,
    InKP (fAct x6 bv (actD σ).1, fAct x6 bv ((actD σ).1 * ((actD σ).2 * (actD σ).2))) 
)
    ∧ (
 ∀ σ ∈ W2,
    InKP (fAct x6 bv (actE σ).1, fAct x6 bv ((actE σ).1 * ((actE σ).2 * (actE σ).2))) 
)
    ∧ (
 ¬ InKP (x6, bv) 
)
    ∧ (
 ∀ d ∈ D6l, Equiv.Perm.sign d = 1 ∧ NormDb d = true 
) := by
  exact ⟨@CertificateChecks.Batch17018.W1_ok_0, @CertificateChecks.Batch17018.W2_ok_1, @CertificateChecks.Batch17018.KP_D_2, @CertificateChecks.Batch17018.KP_E_3, @CertificateChecks.Batch17018.KP_mem1_4, @CertificateChecks.Batch17018.KP_mem2_5, @CertificateChecks.Batch17018.KP_conj1_6, @CertificateChecks.Batch17018.KP_conj2_7, @CertificateChecks.Batch17018.KP_not_v_8, @CertificateChecks.Batch17018.D6_sign_norm_9⟩

end Certificates
