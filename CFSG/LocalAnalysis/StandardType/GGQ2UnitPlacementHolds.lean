module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitPlacement
public import CFSG.LocalAnalysis.StandardType.GGQ2FrameAmbient
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQ2UnitInnerDiagData
import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameExists
import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameRange
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponentsAut
import CFSG.LocalAnalysis.StandardType.GGQ2UnitDiagFixComponents
import CFSG.LocalAnalysis.StandardType.GGQ2UnitBlockDiag
import CFSG.LocalAnalysis.StandardType.GGQ2UnitBlockMarked
import CFSG.LocalAnalysis.StandardType.GGQ2UnitAutomizerAct
import CFSG.LocalAnalysis.StandardType.GGQ2UnitTorusAutFull
import CFSG.LocalAnalysis.StandardType.GGQ2UnitTorusAutHeart

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGQ2Frame.UnitPlacement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem unit_hOcc : UnitComponentOccursIff :=
  unitComponentOccursIff_of CoverComponents.isComponentOfCoverIffAut_holds
    unitIsComponentOfDiagFixIff_holds

private theorem unit_hCent : UnitComponentCentEq :=
  unitComponentCentEq_of CoverComponents.commuteCoverIffAut_holds
    unitBlockPerfect_holds

private theorem unit_hIn : UnitComponentInsideEq :=
  unitComponentInsideEq_of unitBlockPerfect_holds

private theorem unit_hMk : UnitComponentMarked :=
  unitComponentMarked_of unitBlockPerfect_holds unitBlockMarked_holds

section


theorem placementCoreInputOn_unit_holds (ex : FrameKind → RawFrameData) :
    PlacementCoreInputOn (fun lab => lab.tag = .twA) (catalogueOf classicalCatalogue ex) :=
  placementCoreInputOn_unit_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    unitInnerDiagData_holds existsUnitFrame_holds unitFrameRange_holds unit_hOcc unit_hCent
    unit_hIn unit_hMk ex

theorem placementInputOn_unit_holds (ex : FrameKind → RawFrameData) :
    PlacementInputOn (fun lab => lab.tag = .twA) (catalogueOf classicalCatalogue ex) :=
  placementInputOn_unit_of_pieces ggLabelRigidInput_holds ggG0_innerDiag_n_eq_one
    unitInnerDiagData_holds existsUnitFrame_holds unitFrameRange_holds unit_hOcc unit_hCent
    unit_hIn unit_hMk automizerActEq_holds unitAmbientTorusAut_holds unitAmbientTorusAutH_holds
    unitComponentTorusAut_holds unitComponentTorusAutH_holds unitBlockPerfect_holds ex

end

end CFSG.StandardType.GGQ2Frame

end
