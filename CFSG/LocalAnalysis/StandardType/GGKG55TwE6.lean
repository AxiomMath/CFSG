module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryDvd

public section

namespace CFSG.StandardType

theorem ggNbrKGTwE6ThreeAddFive_holds :
    GGNbrKGTwE6ThreeAddFive := by
  intro K _ _ n hn hK h3
  exact ggTorusNoLineComp_of_ggTorusNoLine (ggTorusNoLine_of_noInvariantLineSCr Nat.prime_three
    (ggNoInvariantLineSCr_of_ggTableBModuleSCr (by norm_num)
      (ggTwE6ThreeModuleInput_of_model E6ThreeModel.e6ThreeModel_holds K n hn hK h3)))

end CFSG.StandardType
