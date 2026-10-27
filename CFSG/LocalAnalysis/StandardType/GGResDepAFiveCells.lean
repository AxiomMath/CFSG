module

public import CFSG.LocalAnalysis.StandardType.GGResDepAFive
public import CFSG.LocalAnalysis.StandardType.GGDepACells55
public import CFSG.LocalAnalysis.StandardType.GGDepACells77
public import CFSG.LocalAnalysis.StandardType.GGDepACells510

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResDepAFiveInput_of_cells
    (hKG : GGReflClassLargeInput') (hOrb : GGResCentBoundInput)
    (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput) : GGResDepAFiveInput :=
  ggResDepAFiveInput_of_inputs hKG hOrb hFix hFixK ggDepA_cells_5_5 ggDepA_cells_7_7
    ggDepA_cells_5_10

end CFSG.StandardType
