
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
import Certificates.Kernel.CU43Aut.CentGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate26012 : centCounts = true := KernelCU43Aut.CentG.centCounts_true

end Certificates
