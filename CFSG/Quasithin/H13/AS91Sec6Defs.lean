module

public import CFSG.Quasithin.H13.AS91Sec5Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

@[expose] def Stmt6_5u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    c.G1 ⊔ c.G3 = ⊤

end CFSG.Quasithin.H13.AS91
