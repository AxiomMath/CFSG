module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Co1Tests
import Certificates.Kernel.LocalComp.Co1Fus

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15071 : CFSG.ComponentClassification.AS81.Co1Fusion.fus13Check = true ∧
    CFSG.ComponentClassification.AS81.Co1Fusion.fus11Check = true := KernelLC.Co1Fus.cert15071

end Certificates
