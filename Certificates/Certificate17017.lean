module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDPi
public import Certificates.Certificate2175Base
public import Certificates.Kernel.J4Count.Cent3Checks

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.A5.Delta5 Equiv CFSG.QuasithinUnique.AppC

namespace CertificateChecks.Batch17017

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.A5.Delta5 Equiv CFSG.QuasithinUnique.AppC

private theorem conj_E_cases_0 :  ∀ e ∈ Eset, ∀ g : Perm (Fin 5),
    (e * g * e⁻¹ = 1 ∨ e * g * e⁻¹ = swap 0 1) ↔ (g = 1 ∨ g = swap 0 1)  := by
  decide +kernel

private theorem conj_D_cases_1 :  ∀ σ ∈ Dset, σ ∉ Eset → ∀ g : Perm (Fin 5),
    (σ * g * σ⁻¹ = 1 ∨ σ * g * σ⁻¹ = swap 0 1) ↔ (g = 1 ∨ g = swap 2 3)  := by
  decide +kernel

private theorem swap01_ne_one_2 :  swap (0 : Fin 5) 1 ≠ 1  := by
  decide +kernel

private theorem swap23_ne_one_3 :  swap (2 : Fin 5) 3 ≠ 1  := by
  decide +kernel

private theorem swap01_ne_swap23_4 :  swap (0 : Fin 5) 1 ≠ swap 2 3  := by
  decide +kernel

private theorem fin4_eq_5 :  ∀ i j : Fin 4, ((i = 1 ∨ i = 2) ↔ (j = 1 ∨ j = 2)) →
    ((i = 1 ∨ i = 3) ↔ (j = 1 ∨ j = 3)) → i = j  := by
  decide +kernel

end CertificateChecks.Batch17017

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.AppD CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.A5.Delta5 Equiv CFSG.QuasithinUnique.AppC in
theorem certificate17017 : (
 ∀ e ∈ Eset, ∀ g : Perm (Fin 5),
    (e * g * e⁻¹ = 1 ∨ e * g * e⁻¹ = swap 0 1) ↔ (g = 1 ∨ g = swap 0 1) 
)
    ∧ (
 ∀ σ ∈ Dset, σ ∉ Eset → ∀ g : Perm (Fin 5),
    (σ * g * σ⁻¹ = 1 ∨ σ * g * σ⁻¹ = swap 0 1) ↔ (g = 1 ∨ g = swap 2 3) 
)
    ∧ (
 swap (0 : Fin 5) 1 ≠ 1 
)
    ∧ (
 swap (2 : Fin 5) 3 ≠ 1 
)
    ∧ (
 swap (0 : Fin 5) 1 ≠ swap 2 3 
)
    ∧ (
 ∀ i j : Fin 4, ((i = 1 ∨ i = 2) ↔ (j = 1 ∨ j = 2)) →
    ((i = 1 ∨ i = 3) ↔ (j = 1 ∨ j = 3)) → i = j 
) := by
  exact ⟨@CertificateChecks.Batch17017.conj_E_cases_0, @CertificateChecks.Batch17017.conj_D_cases_1, @CertificateChecks.Batch17017.swap01_ne_one_2, @CertificateChecks.Batch17017.swap23_ne_one_3, @CertificateChecks.Batch17017.swap01_ne_swap23_4, @CertificateChecks.Batch17017.fin4_eq_5⟩

end Certificates
