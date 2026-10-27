module

public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def SporadicFourListDisjoint : Prop :=
  ∀ (X : Type) [Group X] (s : TauCeti.SporadicName), IsSporadic s X → FourList X →
    IsSporadic .M22 X

end CFSG.Quasithin
