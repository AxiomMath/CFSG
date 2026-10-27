module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainShapeBData
import Certificates.Kernel.OmegaEight.T0

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Chain in
theorem certificate3495 : commCheck = true := KernelO8.cert3495

end Certificates

end
