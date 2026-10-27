module

public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem sec7_isSimpleGroup_omegaPlusSix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 3 K)) := by
  obtain ⟨eGS⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv hK
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 K).symm.trans
      (CFSG.SeitzReduction.OmegaPilot.scalars_four_eq_bot_of_charTwo K)
  let eP : Matrix.SpecialLinearGroup (Fin 4) K ≃* StatedProj (StatedSL 4 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 K)
  let eS : ↥(StatedSL 4 K) ≃* StatedProj (StatedSL 4 K) :=
    (specialLinearGroupEquivStatedSL 4 K).symm.trans eP
  haveI : IsSimpleGroup (StatedProj (StatedSL 4 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 4) (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  haveI : IsSimpleGroup ↥(StatedSL 4 K) := eS.isSimpleGroup
  exact eGS.isSimpleGroup

end CFSG.RankThree.GF2n.Stroth80
