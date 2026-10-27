module

import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofKMd
import CFSG.Sporadic.ON
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofFour
public import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17.HeadProof

namespace Proof17Res15

theorem eq_bot_of_types {Γ : Type} [Group Γ] [Finite Γ]
    (htypes : Sec4.IsTripleCover Γ CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Γ (alternatingGroup (Fin 6)) ∨ IsCentralProductA6Covers Γ)
    (W : Subgroup Γ) (hW : W.Normal) (hW3 : ¬ 3 ∣ Nat.card W) : W = ⊥ := by
  rcases htypes with hT | hT | hT
  · have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
    exact Proof17Res8.eq_bot_of_isTripleCover (by rw [CFSG.Sporadic.ON.card_ON]; norm_num) hT W
      hW3
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact Proof17Res8.eq_bot_of_isTripleCover Proof17Res8.three_dvd_card_alternatingGroup_six
      hT W hW3
  · exact Proof17Res8.eq_bot_of_isCentralProductA6Covers hT W hW3

end Proof17Res15

end CFSG.RankThree.PartTwo.Sec17
