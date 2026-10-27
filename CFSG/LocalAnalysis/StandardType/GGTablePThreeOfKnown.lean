module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLA
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUnitary
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTriD4
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeD4
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKGOpenDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section OfKnown

theorem ggTriD4StdSubInput_of_tablePThree
    (h : GGTablePThreeKnown) : GGTriD4StdSubInput :=
  ⟨ggStdSubNotG2Input_of_tablePThree h.1, ggStdSubA2CentreInput_of_tablePThree h.2.1⟩

theorem ggD4OddCentKGInputsOpen_of_offTableP
    (hP : GGTablePThreeKnown)
    (h : GGD4OddCentKGInputsOffTableP) : GGD4OddCentKGInputsOpen :=
  ⟨h.1, h.2.1, ggStdSubNotTriD4Input_of_tablePThree hP.2.2.2.1 h.2.2.2.2,
    ggStdSubNotA1Input_of_tablePThree hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.1,
    ggStdSubTwA2ScalarInput_of_tablePThree hP.2.2.1 hP.2.2.2.2.2.2.2,
    ggStdSubTwA2CentreInput_of_tablePThree hP.2.1, ggStdSubD4Input_of_tablePThree hP.2.2.2.2.1,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end OfKnown

end CFSG.StandardType
