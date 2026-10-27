module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaOrbTests
import Certificates.Kernel.LocalComp.HexaOrb

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15057 : CFSG.ComponentClassification.AS81.Hexa.hexaOrbCheck = true := KernelLC.HexaOrb.hexaOrbCheck_eq

end Certificates
