module

public import CFSG.RankThree.PartTwo.Sec16.Item163Proof
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item15More

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

@[expose] def IsZeta (A L T K : Subgroup G) : Prop :=
  K ∈ scriptY0Star A (lB A) ∧ MeetsY4 A (lB A) L K ∧
    T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2)

structure Conf684 (A : Subgroup G) (c : G) (L Y : Subgroup G) : Prop where
  sec15R : Sec15R G A c L
  mem_y : Y ∈ scriptY0Star A (lB A)
  meets : MeetsY4 A (lB A) L Y
  case3 : Case1514Three A (lB A) c L Y
  item1514 : Item1514 A (lB A) c L
  item143 : Item143N A (lB A)
  item1444 : Item1444 A (lB A)
  item146 : Item146 A (lB A)
  concl142 : Concl142 A (lB A)
  item1411 : Item1411_1 A (lB A)
  item153 : Item153Main A (lB A)
  item155 : Item155 A (lB A)

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
