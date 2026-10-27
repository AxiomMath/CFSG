
module


public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24EBasic
public import Certificates.Certificate10510

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Sporadic.Fi24

theorem mem_fi24EB_of_comm {h : R} (hb : ∀ i, h * bbar i = bbar i * h) : h ∈ fi24EB :=
  Certificates.certificate10510.cent h hb

theorem card_fi24EB_le : Nat.card fi24EB ≤ 4096 :=
  Certificates.certificate10510.card.le

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
