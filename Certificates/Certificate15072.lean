module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7TwoTests

public section

open CFSG

namespace CertificateChecks.Batch15072

open CFSG

private theorem e7ZxX_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckX = true := by
  decide +kernel

private theorem e7ZxY_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckY = true := by
  decide +kernel

private theorem e7ZxZ_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckZ = true := by
  decide +kernel

private theorem e7ZxU_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckU = true := by
  decide +kernel

private theorem e7ZxV_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckV = true := by
  decide +kernel

end CertificateChecks.Batch15072

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15072 : CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckX = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckY = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckZ = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckU = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E7Sec8.e7ZxCheckV = true := by
  exact ⟨CertificateChecks.Batch15072.e7ZxX_check_0, CertificateChecks.Batch15072.e7ZxY_check_0, CertificateChecks.Batch15072.e7ZxZ_check_0,
    CertificateChecks.Batch15072.e7ZxU_check_0, CertificateChecks.Batch15072.e7ZxV_check_0⟩

end Certificates
