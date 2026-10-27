module

public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.Sporadic.Bridge.BPresentation
public import CFSG.YGroups.Y433.Bound

public section

namespace CFSG.Sporadic.Bridge.B

theorem finite_card_le :
    Finite TauCeti.SporadicName.B.Group ∧
    Nat.card TauCeti.SporadicName.B.Group ≤ 4154781481226426191177580544000000 :=
  finite_card_le_of_B433 CFSG.YGroups.B433_finite_card_le.1 CFSG.YGroups.B433_finite_card_le.2

theorem nonempty_mulEquiv
    :
    Nonempty (Blueprint.NativeSporadic.B ≃* TauCeti.SporadicName.B.Group) :=
  nonempty_mulEquiv_of_card_le finite_card_le.1 finite_card_le.2

end CFSG.Sporadic.Bridge.B
