module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Tests
import Certificates.Kernel.LocalComp.Q47Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15054 : CFSG.ComponentClassification.AS81.Q47.q47Check = true := KernelLC.Q47.q47Check_true

end Certificates
