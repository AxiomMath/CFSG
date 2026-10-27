module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModel

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_lcoord_holds :
    C2LCoordLeaf := by
  intro hRig G _ _ p B Bs x L D J y K hH hprime hrow
  exact hdRo7CLCoordAux_coordModel p B Bs x L D J y K hRig hH hrow

end CFSG.StandardType.HdRo7C

end
