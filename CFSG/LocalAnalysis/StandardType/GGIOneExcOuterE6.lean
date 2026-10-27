module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac

public section

namespace CFSG.StandardType

section Certs


theorem ggE6OuterThreeInput_holds : GGE6OuterThreeInput := by
  intro K _ _ n hn hK _ φ hφ hnI
  by_contra h3
  exact hnI (ExcSplitL.mem_chevID_E6_of_pow hn K hK Nat.prime_three (by norm_num) h3 φ hφ)

end Certs

end CFSG.StandardType
