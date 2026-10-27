module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperStatements

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Assembly
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)

@[expose] def FF81TheoremAK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G →
    ∀ b : G, orderOf b = 3 → ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      CFSG.IsQuasisimple L →
      FFCentCyclicSylow L →
      localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
      FFNotWeaklyClosed b →
      FFHypA5 b →
      StatedClassicalModel L .PSp 3 2 1 →
      KProper InCatalog G →
        StatedClassicalModel G .PSp 4 2 1 ∨ ChevalleyExceptionalModel G .F4 2 1

end CFSG.RankThree.PartTwo.Sec21
