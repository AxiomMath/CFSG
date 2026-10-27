module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin

@[expose] def FactOutL34Sp44 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], (IsPSL 3 2 2 Y ∨ IsPSp4 2 2 Y) →
    Nat.card (MulAut Y) ∣ 12 * Nat.card Y

end CFSG.Quasithin.Vol2.Ch10.SecB
