module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwoANarrow21Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpNarrow
public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTorusGenLinTwoNarrow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TableBKnownFormsRestRkOpen20_of_open21
    (h : GGL48TableBKnownFormsRestRkOpen21) : GGL48TableBKnownFormsRestRkOpen20 :=
  ⟨h.1, ggL48TBForm4Rest16_of_restSymp
    (ggL48TBForm4RestSymp_of_restTwE6 (ggL48TBForm4RestTwE6_of_restTwoA h.2.1)), h.2.2⟩

end CFSG.StandardType
