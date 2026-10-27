module

public import CFSG.YGroups.Y433.TwoCentral
import Certificates.Kernel.B433Alt.Bound

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups in
theorem certificate10104 : Finite B433 ∧ Nat.card B433 ≤ 4154781481226426191177580544000000 := KernelB433.B433_finite_card_le

end Certificates
