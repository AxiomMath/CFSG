module

public import CFSG.Quasithin.H13.A6S4ReducedInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6 Equiv CFSG.Open CFSG.QuasithinUnique

namespace CertificateChecks.Batch17016

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6 Equiv CFSG.Open CFSG.QuasithinUnique

private theorem eq_one_of_comm_three_0 :  ∀ σ : Perm (Fin 6),
    σ * (swap 0 1 * swap 1 2) = swap 0 1 * swap 1 2 * σ →
    σ * (swap 3 4 * swap 4 5) = swap 3 4 * swap 4 5 * σ →
    σ * (swap 0 3 * swap 1 4) = swap 0 3 * swap 1 4 * σ → σ = 1  := by
  decide +kernel

private theorem redWit_1 :  ∀ σ : Perm (Fin 6), σ ≠ 1 → RedWit σ  := by
  decide +kernel

private theorem redList_sign_2 :  ∀ τ ∈ RedList, Perm.sign τ = 1  := by
  decide +kernel

private theorem pow_four_of_pow_sixteen_3 :  ∀ σ : Perm (Fin 6), σ ^ 16 = 1 → σ ^ 4 = 1  := by
  decide +kernel

end CertificateChecks.Batch17016

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6 Equiv CFSG.Open CFSG.QuasithinUnique in
theorem certificate17016 : (
 ∀ σ : Perm (Fin 6),
    σ * (swap 0 1 * swap 1 2) = swap 0 1 * swap 1 2 * σ →
    σ * (swap 3 4 * swap 4 5) = swap 3 4 * swap 4 5 * σ →
    σ * (swap 0 3 * swap 1 4) = swap 0 3 * swap 1 4 * σ → σ = 1 
)
    ∧ (
 ∀ σ : Perm (Fin 6), σ ≠ 1 → RedWit σ 
)
    ∧ (
 ∀ τ ∈ RedList, Perm.sign τ = 1 
)
    ∧ (
 ∀ σ : Perm (Fin 6), σ ^ 16 = 1 → σ ^ 4 = 1 
) := by
  exact ⟨@CertificateChecks.Batch17016.eq_one_of_comm_three_0, @CertificateChecks.Batch17016.redWit_1, @CertificateChecks.Batch17016.redList_sign_2, @CertificateChecks.Batch17016.pow_four_of_pow_sixteen_3⟩

end Certificates
