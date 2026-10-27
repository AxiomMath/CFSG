module

public import Certificates.Certificate9353

public section

namespace CFSG.YGroups.DCE.B433

theorem card_centralizer_dY_le
    (hG : 4154781481226426191177580544000000 ≤ Nat.card B433) :
    Nat.card (Subgroup.centralizer {psi dY}) ≤ 306129918735099415756800 :=
  Certificates.certificate9353 hG

end CFSG.YGroups.DCE.B433
