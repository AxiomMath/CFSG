module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainInvData
import Certificates.Kernel.OmegaEight.Orth

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain CFSG.EvenSmallLie.OmegaEight.Stage1 in
theorem certificate3491 : (invCheck .plus = true)
    ∧ (invCheck .minus = true) := KernelO8.cert3491

end Certificates
