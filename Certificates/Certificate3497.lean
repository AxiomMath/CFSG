module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTilData
import Certificates.Kernel.OmegaEight.Til

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight in
theorem certificate3497 : Chain.tilCheck .plus = true ∧ Chain.tilCheck .minus = true := KernelO8.cert3497

end Certificates

end
