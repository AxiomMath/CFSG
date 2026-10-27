module

public import CFSG.YGroups.DCE.B433Rules
public import CFSG.Monster.Existence.TwoPoint.B433CoverNodes
import Certificates.Kernel.B433Alt.CoverB

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.YGroups.DCE.B433 CFSG.Monster.Existence.B433Cover in
theorem certificate6041 : ∀ g : B433, ∃ l < 23, ∃ a ∈ psi.range, ∃ b ∈ psi.range,
    g = a * nodeProd (fun c => psi (yGen 4 3 2 c)) tB l * b := KernelB433.b433_cover

end Certificates
