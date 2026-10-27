module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.J4.Bridge

public section

namespace Certificates

open CertificateChecks

theorem certificate9357 : Finite TauCeti.SporadicName.J4.Group ∧
    Nat.card TauCeti.SporadicName.J4.Group ≤ 86775571046077562880 := KernelBounds.j4

end Certificates
