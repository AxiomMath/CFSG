module

import Certificates.Kernel.J4Count.Fix11
public import CFSG.Sporadic.Schreier.J4SElevenBase

public section

namespace Certificates

open CertificateChecks

theorem certificate12602 :
    ∃ h ∈ CFSG.Sporadic.J4.Hj, orderOf h = 11 ∧
      Nat.card (Subgroup.centralizer ({CFSG.Sporadic.J4Schreier.qx} : Set CFSG.Sporadic.J4.J)) =
        11 * Nat.card ↥(Subgroup.centralizer ({h} : Set CFSG.Sporadic.J4.J) ⊓ CFSG.Sporadic.J4.Hj) := KernelJ4Count.card_centralizer_qx'

end Certificates
