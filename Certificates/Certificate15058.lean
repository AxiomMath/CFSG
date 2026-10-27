module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step48NTests
import Certificates.Kernel.LocalComp.N48Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15058 : CFSG.ComponentClassification.AS81.N48.n48Check = true := KernelLC.N48Check.n48Check_true

end Certificates
