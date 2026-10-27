module

public import CFSG.Quasithin.H13.A7EscapeInputs
public import CFSG.Quasithin.H13.A7HyperplaneBasic

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A7 Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB

namespace CertificateChecks.Batch17011

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A7 Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB

private theorem hammingNorm_vecFour_0 : hammingNorm vecFour = 4 := by
  decide +kernel

private theorem vecFour_mem_1 : vecFour ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide +kernel

end CertificateChecks.Batch17011

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A7 Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB in
theorem certificate17011 : (
 hammingNorm vecFour = 4 
)
    ∧ (
 vecFour ∈ evenWeight 7 
) := by
  exact ⟨@CertificateChecks.Batch17011.hammingNorm_vecFour_0, @CertificateChecks.Batch17011.vecFour_mem_1⟩

end Certificates
