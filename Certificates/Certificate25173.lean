module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23PerfInputs
import Certificates.Kernel.Fi23Pf.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate25173 : CFSG.EvenSporadicStandard.Solomon78.fi23PerfCheck = true := KernelFi23Pf.fi23PerfCheck_true

end Certificates
