module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
import CFSG.RankThree.PartOne.AUTSL.OmegaModel

public section

namespace CFSG.StandardType

open CFSG CFSG.StandardType.Triality
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

namespace D4Inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem bridge_apply_eq_mk (s : Om8 K) :
    (projEquiv8.trans (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge
        (coordinateQuadPlus 4 K) (by norm_num : 0 < 2 * 4))) s =
      QuotientGroup.mk (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
        (coordinateQuadPlus 4 K) s) :=
  CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge_mk _ _ s _ rfl

end D4Inner

end CFSG.StandardType

end
