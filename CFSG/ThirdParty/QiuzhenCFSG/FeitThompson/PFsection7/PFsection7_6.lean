module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_1

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 7: Theorem (7.6)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7
universe u
universe v

@[expose] public def hypothesis_7_6_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L)) : Prop :=
  H ≤ L ∧
    (H.subgroupOf L).Normal ∧
    hypothesis_7_1_statement A L K ∧
    A = puncturedSubgroupSet H ∧
    inducedFamilyNotation (H.subgroupOf L) T

end CFSG.Section7
