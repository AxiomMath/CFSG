module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBDAux

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smModelsBD_holds : SMModelsBDLeaf :=
  ⟨hdRo7SmBDAux_weyl_D7, hdRo7SmBDAux_weyl_B7, hdRo7SmBDAux_weyl_D8, hdRo7SmBDAux_weyl_B8⟩

end CFSG.StandardType.HdRo7SU.Small
