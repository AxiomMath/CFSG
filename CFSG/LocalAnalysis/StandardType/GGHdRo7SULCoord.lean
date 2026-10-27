module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModel

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem su_lcoord_holds :
    SULCoordLeaf := by
  intro hRig G _ _ p B Bs x L D J y K hH _ hrow
  exact hdRo7SULCoordAux_model hH hRig hrow

end CFSG.StandardType.HdRo7SU
