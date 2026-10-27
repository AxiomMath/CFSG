module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8TwoTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8TwoTests

public section

open CFSG

namespace CertificateChecks.Batch15065

open CFSG

private theorem e8ZxX_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckX = true := by
  decide +kernel

private theorem e8ZxY_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckY = true := by
  decide +kernel

private theorem e8ZxZ_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckZ = true := by
  decide +kernel

private theorem e8ZxU_check_0 :
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckU = true := by
  decide +kernel

end CertificateChecks.Batch15065

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15065 : CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckX = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckY = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckZ = true ∧
    CFSG.ComponentClassification.RankTwoExceptional.E8.e8ZxCheckU = true := by
  exact ⟨CertificateChecks.Batch15065.e8ZxX_check_0, CertificateChecks.Batch15065.e8ZxY_check_0, CertificateChecks.Batch15065.e8ZxZ_check_0,
    CertificateChecks.Batch15065.e8ZxU_check_0⟩

end Certificates
