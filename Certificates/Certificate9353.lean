module

public import CFSG.YGroups.DCE.B433Fix
import Certificates.Kernel.B433Alt.FixMain

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.YGroups.DCE.B433 in
theorem certificate9353 : 4154781481226426191177580544000000 ≤ Nat.card B433 →
    Nat.card (Subgroup.centralizer {psi dY}) ≤ 306129918735099415756800 := KernelB433.card_centralizer_dY_le

end Certificates
