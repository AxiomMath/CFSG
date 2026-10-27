module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwE6NarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenTwE6Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TBForm4RestSymp_of_restTwE6
    (h : GGL48TBForm4RestTwE6) : GGL48TBForm4RestSymp := by
  intro p lab hp hlab hS hv h0 hA hT hU
  by_cases hB : GGL48TBTwE6Row p lab
  · exact largeEvenLabelAll_torusGenTableB_twE6 hp hlab hB
  · exact h p lab hp hlab hS hv h0 hA hT hU hB

end CFSG.StandardType
