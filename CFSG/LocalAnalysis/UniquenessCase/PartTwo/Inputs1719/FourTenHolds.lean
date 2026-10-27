module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenLarge
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenPrime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w4Lem4_10F_holds :
    W4Lem4_10F :=
  w4Lem4_10F_of fourTenLarge_holds fourTenPrime_holds fourTenNine_holds

theorem w4Lem4_10_holds :
    W4Lem4_10 :=
  w4Lem4_10_of w4Lem4_10F_holds w4Lem4_10Small_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
