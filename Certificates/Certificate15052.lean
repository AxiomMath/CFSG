module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaTests
import Certificates.Kernel.LocalComp.HexaCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15052 : CFSG.ComponentClassification.AS81.Hexa.hexaCheck = true := KernelLC.HexaCheck.hexaCheck_true

end Certificates
