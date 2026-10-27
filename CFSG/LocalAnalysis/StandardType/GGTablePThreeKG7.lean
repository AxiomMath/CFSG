module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU6OfR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU6OnR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU5OfR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeU5OnR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePThreeU6NoTwoGroupKnown_holds :
    GGTablePThreeU6NoTwoGroupKnown :=
  TablePThreeKG.u6_of_R TablePThreeKG.uni6_kg7_on_R_holds

theorem ggTablePThreeU5NoTwoGroupKnown_holds :
    GGTablePThreeU5NoTwoGroupKnown :=
  TablePThreeKG.u5_of_R TablePThreeKG.uni5_kg7_on_R_holds

theorem ggTablePThreeKnownRest_of_restSix
    (h : GGTablePThreeKnownRestSix) : GGTablePThreeKnownRest :=
  ggTablePThreeKnownRest_of_six h ggTablePThreeU6NoTwoGroupKnown_holds
    ggTablePThreeU5NoTwoGroupKnown_holds

end CFSG.StandardType

end
