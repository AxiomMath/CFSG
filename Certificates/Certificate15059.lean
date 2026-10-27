module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
import Certificates.Kernel.LocalComp.B0SuzProof

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15059 : CFSG.ComponentClassification.AS81.SuzB0.b0SuzCheck = true := KernelLC.B0Suz.b0SuzCheck_true

end Certificates
