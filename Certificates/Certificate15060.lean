module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabTests
import Certificates.Kernel.LocalComp.HexaStabCheck

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15060 : CFSG.ComponentClassification.AS81.Hexa.hexaStabCheck = true :=
  KernelLC.HexaStabCheck.hexaStabCheck_true

end Certificates
