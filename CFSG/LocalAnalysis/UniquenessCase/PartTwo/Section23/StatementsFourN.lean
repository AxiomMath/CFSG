module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_4_inputN (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    ⁅(X23_4 D c.N ⊓ D.M), (X23_4 D c.N ⊓ D.M)⁆ ≤ centralizer (D.U : Set G) ∧
      IrrOn (X23_4 D c.N ⊓ D.M) D.U

end CFSG.LocalAnalysis.UniquenessCase.UC22
