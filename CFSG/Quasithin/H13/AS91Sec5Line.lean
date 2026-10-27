module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

@[expose] def Stmt5_LineU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 → c.G1 ⊓ stabilizer G y ≤ c.G2

end CFSG.Quasithin.H13.AS91
