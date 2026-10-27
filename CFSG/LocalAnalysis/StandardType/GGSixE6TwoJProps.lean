module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoJEq
import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
import CFSG.LocalAnalysis.StandardType.GGHalfFiveLayer
import CFSG.Timmesfeld.RankTwo.Presentation

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section JFacts

private noncomputable def jEquiv : Matrix.SpecialLinearGroup (Fin 3) F4 ≃* ↥jE :=
  sl3fourEquiv.trans
    ((Subgroup.equivMapOfInjective sl3four (E6Pilot.slToAdjointE6 F2) iota_injective).trans
      (MulEquiv.subgroupCongr jE_eq.symm))

theorem isQuasisimple_jE : CFSG.Assembly.IsQuasisimple ↥jE := by
  have hSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F4) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup
      (n := 3) (K := F4) (by norm_num)
  have h := CFSG.IsQuasisimple.of_mulEquiv jEquiv.symm hSL
  exact ⟨Group.isPerfect_def.mp h.1, h.2.1⟩

end JFacts

end CFSG.StandardType.GGSixE6Two
