module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpNarrowDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggL48TBForm4Rest16_of_restSymp
    (h : GGL48TBForm4RestSymp) :
    GGL48TBForm4Rest16 := by
  intro p lab hp hlab hS hv hT hA hU
  by_cases hB : GGTableBSympLabel p lab
  · exact largeEvenLabelAll_torusGenTableB_symplectic hp hlab hB
  · exact h p lab hp hlab hS hv hT hA hU hB

end CFSG.StandardType
