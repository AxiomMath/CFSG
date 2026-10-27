module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23KInputs
import Certificates.Kernel.Fi23Kt.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate27301 : CFSG.EvenSporadicStandard.HypOne.Fi23.fi23KCheck = true := KernelFi23Kt.fi23KCheck_true

end Certificates
