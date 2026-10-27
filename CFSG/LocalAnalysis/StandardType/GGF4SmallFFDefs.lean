module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FF81bThmAAtFiveSixLab
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    IsCharTwoType G → KProper InCatalog G → ∀ n : ℕ, (n = 5 ∨ n = 6) → ∀ b : G, orderOf b = 3 →
      ∀ L : Subgroup G,
      L ≤ Subgroup.centralizer ({b} : Set G) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) →
      StatedClassicalModel L .PSL (n + 1) 2 1 →
      (∀ P : Sylow 3 ↥(Subgroup.centralizer (L : Set G)), IsCyclic P) →
      twoLocalPrimeRank 3 G = twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b} : Set G)) →
      CFSG.RankThree.PartTwo.Sec21.FFNotWeaklyClosed b →
        StatedClassicalModel G .PSL (n + 3) 2 1 ∨
          (n = 5 ∧ GGHasLabel ⟨.E6, 0, 1⟩ (G ⧸ Subgroup.center G))

end CFSG.StandardType

end
