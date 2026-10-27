module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bLift
import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCover
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem false_of_norm2e {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L E F : Subgroup G} {a b : G} {R Y : Subgroup G} (hY : YCfg G A c L E F a b R Y)
    {X : Type} [Group X] (hX : Norm2e X)
    (e : haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
      Nonempty (Y ⧸ solvableRadical Y ≃* X)) : False := by
  haveI : (solvableRadical Y).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨e₂⟩ := e
  have hYc : Y ∈ thetaComponentsAt 3 b := hY.hD.mem_thetaComponentsAt
  have hq : CFSG.IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hYc
  obtain ⟨e₁⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := Y) hq
  have hθ : aschbacherSolvableCore 3 (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ :=
    (theta_quotient_core_and_ranks (G := Y)).1
  have hZ : IsPGroup 3 (Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y)) :=
    Sec10.Sec10XProof.isPGroup_center_of_theta_eq_bot hθ
  have hN : Norm2e (Y ⧸ aschbacherSolvableCore 3 Y) :=
    norm2e_of_center_quotient hZ (e₁.trans e₂) hX
  have hbY : b ∈ Sec4.thetaQuotCentralizer Y :=
    Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hYc
  exact hY.hE (partTwoE_of_norm2e hY.hCfg.hEe hY.hCfg.hE27 hY.hbE hY.hD.ne_one hbY hY.hEY hN)

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
