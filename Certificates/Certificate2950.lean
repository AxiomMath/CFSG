module

public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Certificate8950

public section

open Subgroup Equiv

namespace CertificateChecks.Batch2950

open Subgroup Equiv

private theorem conj_gen1_0 : (swap 3 4 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 3 4 := by
  decide +kernel

private theorem y_normalizes_1 : (swap 2 3 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 2 3 := by
  decide +kernel

private theorem y_normalizes_2 : (swap 3 4 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 3 4 := by
  decide +kernel

private theorem y_normalizes_3 : (swap 4 5 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 4 5 := by
  decide +kernel

end CertificateChecks.Batch2950

namespace Certificates

open CertificateChecks

open Subgroup Equiv in
theorem certificate2950 : ((swap 3 4 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 3 4)
    ∧ ((swap 2 3 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 2 3)
    ∧ ((swap 3 4 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 3 4)
    ∧ ((swap 4 5 : Perm (Fin 6)) * swap 0 1 = swap 0 1 * swap 4 5) := by
  exact ⟨CertificateChecks.Batch2950.conj_gen1_0, CertificateChecks.Batch2950.y_normalizes_1, CertificateChecks.Batch2950.y_normalizes_2, CertificateChecks.Batch2950.y_normalizes_3⟩

end Certificates
