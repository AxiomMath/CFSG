module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSData
import Certificates.Kernel.OmegaEight.SM3870

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3870 : (sRangeCheck = true)
    ∧ (sAssocCheck = true)
    ∧ (sUnitCheck = true)
    ∧ (sActCheck = true) := KernelO8.SM3870.cert3870

end Certificates
