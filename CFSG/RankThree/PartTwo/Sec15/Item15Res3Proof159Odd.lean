module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof159

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Step159Y0NotTrans : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → CFSG.Open.pCoreOf 2 L = ⊥ →
      ¬ TransOn A (lB A) (xA A) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

end CFSG.RankThree.PartTwo.Sec15
