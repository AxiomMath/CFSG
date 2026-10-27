module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeData
import Certificates.Kernel.OmegaEight.Cone

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight in
theorem certificate3496 : Chain.splitConeCheck .plus = true ∧ Chain.splitConeCheck .minus = true := KernelO8.cert3496

end Certificates
