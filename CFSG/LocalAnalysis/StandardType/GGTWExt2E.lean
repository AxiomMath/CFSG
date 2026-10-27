module

public import CFSG.LocalAnalysis.StandardType.GGTWExt2Defs

public section

namespace CFSG.StandardType

theorem ggTWExt2All_E6 : GGTWExt2All CoxeterMatrix.E₆ :=
  ggTWExt2All_of_check (by decide +kernel)

theorem ggTWExt2All_E8 : GGTWExt2All CoxeterMatrix.E₈ :=
  ggTWExt2All_of_check (by decide +kernel)

theorem ggTWExt2All_F4 : GGTWExt2All CoxeterMatrix.F₄ :=
  ggTWExt2All_of_check (by decide +kernel)

end CFSG.StandardType

end
