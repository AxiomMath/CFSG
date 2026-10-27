module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OrbitInputs
import Certificates.Kernel.Co1Cover.Bridge24550

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoCo1 in
theorem certificate24550 :
    (orbitCheck11 eMaskC 1288 [] = true)
    ∧ (orbitCheck11 eMaskA 759 [eMaskC] = true)
    ∧ (coverCheck11 = true) := KernelCo1Cover.ECore.facts24550

end Certificates
