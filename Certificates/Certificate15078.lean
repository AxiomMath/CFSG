module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTypeInputs
import Certificates.Kernel.LocalComp.B0SuzProof

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15078 : CFSG.ComponentClassification.AS81.SuzB0.shatTypeCheck = true := KernelLC.B0Suz.shatTypeCheck_true

end Certificates
