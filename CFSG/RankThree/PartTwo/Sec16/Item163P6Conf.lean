module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
public import CFSG.RankThree.PartTwo.Sec13.Item138N

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G]

structure Conf685 (A : Subgroup G) (c : G) (L Y S : Subgroup G) : Prop where
  sec15R : Sec15R G A c L
  le_y : ∀ Y₀ ∈ scriptY0Star A (lB A), L ≤ Y₀
  pCoreOf_eq_bot : CFSG.Open.pCoreOf 2 L = ⊥
  not_isL3TwoPow : ¬ IsL3TwoPow L
  mem_y : Y ∈ scriptY0Star A (lB A)
  mem_s : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (Y : Set G)) (piOf 2)
  mem_d : S ⊓ L ∈ scriptQPiStar A (lB A) L (piOf 2)
  d_ne_bot : S ⊓ L ≠ ⊥
  item1514 : Item1514 A (lB A) c L
  meets : Step163Meets
  l4a7 : Step163L4A7
  item131 : Item131
  item138 : Item138N
  item153 : Item153Main A (lB A)
  obs : Claim153Obs A (lB A)
  item1411 : Item1411_1 A (lB A)
  concl142 : Concl142 A (lB A)
  item1444 : Item1444 A (lB A)
  item146 : Item146 A (lB A)
  bot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥

end CFSG.RankThree.PartTwo.Sec16.Proof163P6
