module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2: Theorem (2.2)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2
universe u

/-! ## (2.2) -/

/-- Peterfalvi (2.2), restated as the `Hypothesis2` structure from `Basic`. -/
@[expose] public def hypothesis_2_2_statement {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) : Prop :=
  Hypothesis2 A L H

end CFSG.Section2
