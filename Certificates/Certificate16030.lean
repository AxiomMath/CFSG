module

public import CFSG.Monster.Existence.EbCheck

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16030

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

private theorem rhoEquiv_qP_one_sixty_sixty_mem_frameInv_0 : packP (false, 60, 60) ≠ 0 := by
  decide +kernel

private theorem rhoEquiv_qP_one_sixty_sixty_mem_frameInv_1 :
    qX (packP (false, 60, 60)) = false := by
  decide +kernel

private theorem rhoEquiv_qP_one_three_fortyeight_mem_frameInv_2 : packP (false, 3, 48) ≠ 0 := by
  decide +kernel

private theorem rhoEquiv_qP_one_three_fortyeight_mem_frameInv_3 :
    qX (packP (false, 3, 48)) = false := by
  decide +kernel

private theorem rhoEquiv_qP_one_734_zero_mem_frameInv_4 : packP (false, 734, 0) ≠ 0 := by
  decide +kernel

private theorem rhoEquiv_qP_one_734_zero_mem_frameInv_5 :
    qX (packP (false, 734, 0)) = false := by
  decide +kernel

end CertificateChecks.Batch16030

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census in
theorem certificate16030 : (
    packP (false, 60, 60) ≠ 0
  ) ∧ (
    qX (packP (false, 60, 60)) = false
  ) ∧ (
    packP (false, 3, 48) ≠ 0
  ) ∧ (
    qX (packP (false, 3, 48)) = false
  ) ∧ (
    packP (false, 734, 0) ≠ 0
  ) ∧ (
    qX (packP (false, 734, 0)) = false
  ) := by
  exact ⟨CertificateChecks.Batch16030.rhoEquiv_qP_one_sixty_sixty_mem_frameInv_0,
    CertificateChecks.Batch16030.rhoEquiv_qP_one_sixty_sixty_mem_frameInv_1,
    CertificateChecks.Batch16030.rhoEquiv_qP_one_three_fortyeight_mem_frameInv_2,
    CertificateChecks.Batch16030.rhoEquiv_qP_one_three_fortyeight_mem_frameInv_3,
    CertificateChecks.Batch16030.rhoEquiv_qP_one_734_zero_mem_frameInv_4,
    CertificateChecks.Batch16030.rhoEquiv_qP_one_734_zero_mem_frameInv_5⟩

end Certificates
