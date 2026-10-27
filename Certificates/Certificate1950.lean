module

public import CFSG.Quasithin.Recognition.M12AscL2

public section

open CFSG CFSG.Quasithin Equiv

namespace CertificateChecks.Batch1950

open CFSG CFSG.Quasithin Equiv

private theorem z_mem_N_0 : NormDb (swap 0 1) = true := by
  decide +kernel

private theorem up_mem_N_1 : NormDb (swap 4 5) = true := by
  decide +kernel

private theorem b_mem_N_2 : NormDb pb = true := by
  decide +kernel

end CertificateChecks.Batch1950

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin Equiv in
theorem certificate1950 : (NormDb (swap 0 1) = true)
    ∧ (NormDb (swap 4 5) = true)
    ∧ (NormDb pb = true) := by
  exact ⟨CertificateChecks.Batch1950.z_mem_N_0, CertificateChecks.Batch1950.up_mem_N_1, CertificateChecks.Batch1950.b_mem_N_2⟩

end Certificates
