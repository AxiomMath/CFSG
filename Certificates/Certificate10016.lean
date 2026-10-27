module

public import CFSG.LieType.Multipliers.U62SylowInputs
import Certificates.Kernel.Multipliers.U62Upper

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.LieType.Multipliers.U62 in
theorem certificate10016 : Finite (PG 4 cover₁) ∧ Nat.card (PG 4 cover₁) ≤ 13685760 := KernelU62.cover₁_card_le

end Certificates
