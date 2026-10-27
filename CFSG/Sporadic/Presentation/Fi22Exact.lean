module

public import CFSG.Sporadic.Presentation.Fi22ExactChain

public section

namespace CFSG.Sporadic.Presentation.Fi22

open CFSG.Sporadic.Presentation.Fi22Exact

theorem finite_card_le :
    Finite TauCeti.SporadicName.Fi22.Group ∧
    Nat.card TauCeti.SporadicName.Fi22.Group ≤ 64561751654400 :=
  card_presented_Fi22_le

end CFSG.Sporadic.Presentation.Fi22
