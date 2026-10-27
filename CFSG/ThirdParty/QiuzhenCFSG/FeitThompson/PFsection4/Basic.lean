module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: basic notation

This file records the book-facing vocabulary for Peterfalvi, Section 4,
`The Dade Isometry for a Certain Type of Subgroup`.

No BG results are imported here.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4

universe u

@[expose] public def pairwiseOrthogonal4 {X : Type u} [Group X] [Finite X]
    (α β γ δ : Section1.ClassFunction X) : Prop :=
  Section1.scalarProduct X α β = 0 ∧
    Section1.scalarProduct X α γ = 0 ∧
    Section1.scalarProduct X α δ = 0 ∧
    Section1.scalarProduct X β γ = 0 ∧
    Section1.scalarProduct X β δ = 0 ∧
    Section1.scalarProduct X γ δ = 0

end CFSG.Section4
