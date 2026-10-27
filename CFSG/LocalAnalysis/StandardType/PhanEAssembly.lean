module

public import CFSG.LocalAnalysis.StandardType.PhanELocalFinal
public import CFSG.LocalAnalysis.StandardType.PhanEDMThm66
public import CFSG.LocalAnalysis.StandardType.PhanELift
public import CFSG.LocalAnalysis.StandardType.PhanEStdChoice

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE


theorem phanEInput2_of_classified
    (cfg : PhanEConfigChoice)
    (h1 : PhanEClassified cfg) (h3 : PhanEBridge cfg) : PhanEInput2 :=
  phanEInput2_of_parts cfg (phanELocal_of_classified cfg h1) DM.dm07Thm66 h3 phanELift_holds

section Std


theorem phanEInput2_of_stdClassified (h1 : PhanEClassified stdChoice) : PhanEInput2 :=
  phanEInput2_of_classified stdChoice h1 phanEBridge_stdChoice

end Std

end CFSG.ClassicalInvolution.Phan.PhanE

end
