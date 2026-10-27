module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitZData
import Certificates.Kernel.OmegaEight.Til

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight in
theorem certificate3498 : Chain.zCheck .plus = true ∧ Chain.zCheck .minus = true := KernelO8.cert3498

end Certificates

end
