module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U33AutE8
import CFSG.GH74.KGroups.AutModelIndexTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.AutE8U33Facts
import CFSG.Adapters.GeneralizedFitting
import CFSG.ClassicalInvolution.SubnormalClosure
import CFSG.GH74.Uniqueness.Section14Card
import CFSG.LieType.Multipliers.ThreeThreeCenter
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.KGroups.U33Inputs
public import CFSG.GroupTheory.E8GenFacts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.GH74.KGroups.U33

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.GroupTheory CFSG.GH74.KGroups

theorem k_U33AutE8_holds :
    K_U33AutE8 := by
  intro Y _ _ hq hU
  change E8GenFacts Y
  let F := genFittingFStar Y
  have hFnormal : F.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal Y
  have hZ : Subgroup.center ↥F = ⊥ :=
    CFSG.LieType.Multipliers.center_eq_bot_of_lieModel_psu_three_three hq hU
  have hN : Subgroup.centralizer (F : Set Y) = ⊥ :=
    (inf_eq_right.mpr (CFSG.Adapters.generalized_fitting_self_centralizing Y)).symm.trans
      (CFSG.GH74.Uniqueness.inf_centralizer_eq_bot_of_center F hZ)
  obtain ⟨e1⟩ := U33.equiv_of_lieModel (K := ↥F ⧸ Subgroup.center ↥F) hU
  let e : ↥F ≃* U33.QP.originalSubgroup :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e1
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have h2 : Nat.card M.A = 2 * Nat.card M.P := by
    rw [hMA, hMP, card_group U33.QA U33.QA_ok, card_group U33.QP U33.QP_ok,
      U33.QA_valid.2, U33.QP_valid.2]
  have hA : E8GenFacts ↥M.A := by
    rw [hMA]
    exact AutE8U33.e8GenFacts_QA
  have hP : ∀ B : Subgroup (Equiv.Perm (Fin 28)), B ≤ M.P →
      (∀ b ∈ B, b ^ 2 = 1) → ¬ 8 ≤ Nat.card B := by
    intro B hB hB2
    rw [hMP] at hB
    exact AutE8U33.not_eight_le_card_of_le_QP B hB hB2
  exact CFSG.GH74.KGroups.AutModel.e8GenFacts F hN M h2 hA hP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
