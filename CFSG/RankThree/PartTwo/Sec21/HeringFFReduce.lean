module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFCore
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FFCentralizerNormalizes : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → IsL4L5Sp6 X → CFSG.IsQuasisimple X →
      Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G)

@[expose] def FFSylowIsAL45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X →
    (StatedClassicalModel (lBar X) .PSL 4 2 1 ∨ StatedClassicalModel (lBar X) .PSL 5 2 1) →
    CFSG.IsQuasisimple X → Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
    ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) →
      ∃ P : Sylow 3 ↥(Subgroup.centralizer ({a} : Set G)),
        (P : Subgroup ↥(Subgroup.centralizer ({a} : Set G))).map
          (Subgroup.centralizer ({a} : Set G)).subtype = A

end CFSG.RankThree.PartTwo.Sec21
