module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Check
import Certificates.Kernel.HJ12.Orbits
import CFSG.Certificates.Kernel.HJ12OrbSound

public section

namespace Certificates

open CertificateChecks

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12 in
theorem certificate17291 : (hjOrbitCheck = true) ∧ (hjS1Check = true) ∧ (hjS2Check = true) ∧
    (hjGammaCheck = true) :=
  ⟨Certificates.Kernel.HJ12K.hjOrbitCheck_of KernelHJ12.ch17291_orb,
    Certificates.Kernel.HJ12K.hjS1Check_of KernelHJ12.ch17291_s1,
    Certificates.Kernel.HJ12K.hjS2Check_of KernelHJ12.ch17291_s2,
    Certificates.Kernel.HJ12K.hjGammaCheck_of KernelHJ12.ch17291_gam⟩

end Certificates
