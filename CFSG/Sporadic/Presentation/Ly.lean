module

public import CFSG.Sporadic.Presentation.LyInputs
public import Certificates.Certificate9120

public section

namespace CFSG.Sporadic.Presentation.Ly

theorem finite_card_le : Finite TauCeti.SporadicName.Ly.Group ∧
    Nat.card TauCeti.SporadicName.Ly.Group ≤ 51765179004000000 :=
  Certificates.certificate9120

end CFSG.Sporadic.Presentation.Ly
