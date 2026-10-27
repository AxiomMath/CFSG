module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 3: Theorem (3.3)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section3
universe u
universe v

/-! ## (3.3) -/

/--
Peterfalvi Notation (3.3), represented as an explicit indexed system of the
irreducible characters `ωᵢⱼ` of `W`; the base row and column are exactly the
irreducibles whose kernels contain the opposite direct factor.
-/
@[expose] public def notation_3_3_statement
    {G : Type u} [Group G] [Finite G]
    (W1 W2 W : Subgroup G)
    (I J : Type*) [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W) : Prop :=
  OmegaSystem W1 W2 W I J i0 j0 ω

end CFSG.Section3
