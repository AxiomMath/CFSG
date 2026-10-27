module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Q0SuzTests
import Certificates.Kernel.LocalComp.B0SuzProof

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15061 : CFSG.ComponentClassification.AS81.SuzB0.q0SuzCheck = true := KernelLC.B0Suz.q0SuzCheck_true

end Certificates
