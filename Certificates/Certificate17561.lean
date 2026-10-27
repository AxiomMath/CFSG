module

import Certificates.Kernel.B433Alt.FCentMain
public import CFSG.YGroups.Model432F

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.Certificates.CosetEnumeration in
theorem certificate17561 : 
    Nat.card ↥(Subgroup.centralizer {rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5])} ⊓
        rho432F.range) ≤ 25200 ∧
      orderOf (rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5])) = 5 ∧
      ∃ e : YGroup 4 3 2, orderOf (rho432F e) = 7 ∧
        rho432F e * rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5]) =
          rho432F (evalWord (yGen 4 3 2) [1, 2, 0, 5]) * rho432F e :=
  KernelB433.card_centralizer_five

end Certificates
