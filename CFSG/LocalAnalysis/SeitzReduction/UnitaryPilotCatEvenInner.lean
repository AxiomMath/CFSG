module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf

theorem catSUmEvenInner :
    CatSUmEvenInner := by
  intro S _ _ hS hna heven σ hσ hin m f D hD _
  have := hS
  exact F4Pilot.false_of_isComponent_fixedSubgroup_inner hna
    (involutionCentralizersComponentFree_of_evenLieType heven) hσ hin hD

end CFSG.SeitzReduction.UnitaryPilot
