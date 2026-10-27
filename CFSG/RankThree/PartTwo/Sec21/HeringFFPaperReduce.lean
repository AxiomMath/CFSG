module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFPaperStatements
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.HeringFFCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FFCentCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → IsL4L5Sp6 X → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) → FFCentCyclicSylow X

@[expose] def FFLocalRankC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → IsL4L5Sp6 X → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
      localRank 3 G = localRank 3 ↥(Subgroup.centralizer ({a} : Set G))

@[expose] def FFPRankL5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → StatedClassicalModel (lBar X) .PSL 5 2 1 → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
    ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) →
      localRank 3 G = CFSG.Open.pRank 3 (Subgroup.centralizer ({a} : Set G))

@[expose] def FFStandardJL5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → StatedClassicalModel (lBar X) .PSL 5 2 1 → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) → FFStandardJ a X

@[expose] def FFHypA5Sp6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → StatedClassicalModel (lBar X) .PSp 3 2 1 → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
    ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) →
      FFHypA5 a

@[expose] def FFCenterSp6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (a : G) (X : Subgroup G),
    Sec21Point G A a X → StatedClassicalModel (lBar X) .PSp 3 2 1 → CFSG.IsQuasisimple X →
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) →
    ¬ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) →
      StatedClassicalModel X .PSp 3 2 1

end CFSG.RankThree.PartTwo.Sec21
