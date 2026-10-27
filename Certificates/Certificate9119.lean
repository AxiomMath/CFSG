module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.J3.Bridge

public section

namespace Certificates

open CertificateChecks

theorem certificate9119 : Finite TauCeti.SporadicName.J3.Group ∧ Nat.card TauCeti.SporadicName.J3.Group ≤ 50232960 := KernelJ3.j3

end Certificates
