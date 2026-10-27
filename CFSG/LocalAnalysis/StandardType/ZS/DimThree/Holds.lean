module

public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Main

public section

namespace CFSG.StandardType.ZS.DimThree


theorem dimThreeCase_holds : DimThreeCase :=
  fun _ _ _ _ _ _ _ hp h3 hR hI hprim => family_of_finrank_eq_three hp h3 hR hI hprim

end CFSG.StandardType.ZS.DimThree
