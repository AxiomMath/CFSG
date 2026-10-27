module

public import CFSG.YGroups.DCE.B433Rules
import Certificates.Kernel.B433Alt.MaxB

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.YGroups.DCE.B433 in
theorem certificate9354 : 4154781481226426191177580544000000 ≤ Nat.card B433 →
    ∀ L : Subgroup B433, psi.range ≤ L → L = psi.range ∨ L = ⊤ := KernelB433.psi_range_maximal

end Certificates
