module

public import CFSG.RankThree.PartTwo.Sec15.Item155ProofDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

structure Data155N (A L X Y M T P J : Subgroup G) : Prop where
  mem_p : P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (J : Set G)) (piOf 2)
  le_tp : T ≤ P
  le_qp : CFSG.Open.pCoreOf 2 (P ⊔ J) ≤ P
  norm_rq : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (P ⊔ J) : Set G)
  case_a : ⁅CFSG.Open.pCoreOf 2 Y, J⁆ ≤ CFSG.Open.pCoreOf 2 J →
    CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 (P ⊔ J)
  case_two : (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    ¬ (Case154Two L J X ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X))
  case_b : Case154Three A L J X (CFSG.Open.pCoreOf 2 Y) → Hyp322 (P ⊔ J) (CFSG.Open.pCoreOf 2 Y)

structure End155N (A X K Y M T P : Subgroup G) : Prop where
  mem_x : X ∈ thetaComponentsIn M
  mem_p : P ∈ scriptQPiStar A (lB A) (M ⊓ Subgroup.normalizer (X : Set G)) (piOf 2)
  le_tp : T ≤ P
  eq_rq : CFSG.Open.pCoreOf 2 Y = CFSG.Open.pCoreOf 2 (P ⊔ X)
  claim : Claim155 A K Y

end CFSG.RankThree.PartTwo.Sec15
