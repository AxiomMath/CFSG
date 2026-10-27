module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Co2.Kill
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelCo2

theorem co2 : Finite TauCeti.SporadicName.Co2.Group ∧
    Nat.card TauCeti.SporadicName.Co2.Group ≤ 42305421312000 :=
  co2_bound

end CertificateChecks.KernelCo2

end
