
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Inputs
import Certificates.Kernel.CU43Aut.SylGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.M24Std.CU43 in
theorem certificate26011 : cosetCounts = true := KernelCU43Aut.SylG.cosetCounts_true

end Certificates
