module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 7: Theorem (7.4)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7
universe u
universe v

@[expose] public def hypothesis_7_4_statement
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (A : I → Set G)
    (L : I → Subgroup G)
    (H : I → G → Subgroup G)
    (G0 : Set G) : Prop :=
  familyHypothesis A L H ∧
    G0 = (Set.univ \ ⋃ i, dadeProjectionSupport (A i) (H i))

end CFSG.Section7
