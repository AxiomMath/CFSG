module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
import CFSG.ClassicalInvolution.Uniform.U9G2
import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.Q27 (InvolutionCentralizersGenerate)


theorem involutionCentralizersGenerate_g2_three {X : Type} [Group X]
    (hm : CFSG.Models.LieModel X .G2 0 3 1) : InvolutionCentralizersGenerate X := by
  have hadm := hm.1
  have hp : (3 : ℕ).Prime := hadm.1
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm
  obtain ⟨-, hY⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .G2 0 3 1 hp
    trivial hadm
  obtain ⟨eX⟩ := CFSG.ClassicalInvolution.Upgrade.lieModel_unique (t := .G2) (by norm_num) trivial
    hB hY
  have hZ := CFSG.ClassicalInvolution.RouteD.center_modelUniv_G2 0 3 1 hp
  let eK : (modelUniv .G2 0 3 1 hp).K ⧸ center (modelUniv .G2 0 3 1 hp).K ≃*
      (modelUniv .G2 0 3 1 hp).K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine involutionCentralizersGenerate_of_mulEquiv (eK.symm.trans eX.symm) ?_
  intro u v hu hv hu1 hv1 huv hc
  rw [CFSG.ClassicalInvolution.Uniform.g2_pairGen3_proved u v hu hv hu1 hv1 huv hc, top_sup_eq]

theorem seitzFourInner_g2_three :
    SeitzFourInner fun X _ => CFSG.Models.LieModel X .G2 0 3 1 :=
  seitzFourInner_of_involutionCentralizersGenerate fun _ _ hX =>
    involutionCentralizersGenerate_g2_three hX

end CFSG.LocalAnalysis.WeakClosure81

end
