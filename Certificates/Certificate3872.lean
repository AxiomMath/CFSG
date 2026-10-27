module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
import Certificates.Kernel.OmegaEight.SB3872C
public import Certificates.Certificate3086

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.SpBranch in
theorem certificate3872 : t1EnumCheck = true := KernelO8.SB3872.enum_check

end Certificates
