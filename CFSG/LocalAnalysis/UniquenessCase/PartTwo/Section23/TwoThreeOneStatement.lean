module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_1ABound (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, ∀ V : Subgroup G, V ≤ c.V → V = conjClosure c.N (V ⊓ D.Z) →
    V ≠ ⊥ → ∀ hW : IsElemAbelian 2 (conjClosure c.L0 (V ⊓ D.Z)),
      aBar (c.L0 ⊔ D.T) ⊥ (conjClosure c.L0 (V ⊓ D.Z)) hW ≤ c.n

end CFSG.LocalAnalysis.UniquenessCase.UC22
