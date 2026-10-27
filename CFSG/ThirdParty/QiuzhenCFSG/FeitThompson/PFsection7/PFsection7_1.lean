module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 7: Theorem (7.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7
universe u
universe v

@[expose] public def hypothesis_7_1_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) : Prop :=
  Section2.hypothesis_2_2_statement A L H

end CFSG.Section7
