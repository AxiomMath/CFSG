module

public import CFSG.Quasithin.Recognition.L34AmalgamCasesInputs
import Certificates.Kernel.LocalComp.WittA7035

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign in
open CFSG.Quasithin.Asc94 in
theorem certificate7035 :
    (∀ s ∈ cbWords, evalW gen (word s) * bT1 = bT1 * evalW gen (word s))
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ ¬ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
       (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ bTabs, ∀ x : Fin 22,
         T.getD (σ x).val 0 = (tab bT1).getD (T.getD x.val 0).val 0) = 0)
    ∧ (m22Count (fun σ => σ 0 = 0 ∧ σ 1 ≠ 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
       (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ cbTabs, ∃ R ∈ repTabs, ∀ x : Fin 22,
         T.getD (σ x).val 0 = R.getD (T.getD x.val 0).val 0) = 0) :=
  ⟨KernelLC.Witt.cb_comm, KernelLC.Witt.count_C1, KernelLC.Witt.count_C2⟩

end Certificates
