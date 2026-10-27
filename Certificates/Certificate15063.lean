module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step44Tests
import Certificates.Kernel.LocalComp.Step44Check

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15063 : CFSG.ComponentClassification.AS81.Hexa.step44Check = true := KernelLC.Step44Check.step44Check_true

end Certificates
