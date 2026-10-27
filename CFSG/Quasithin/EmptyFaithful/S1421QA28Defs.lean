module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

@[expose] def Rank2TwoPart : Prop :=
  ∀ (X : Type) [Group X], IsRank2LieChar2 X → Nat.card X = 168 ∨ 2 ^ 6 ∣ Nat.card X

end CFSG.Quasithin
