module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSeven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCox

public section

namespace CFSG.StandardType.QTwo

section Producer


theorem ggSecFivePhanDQTwoSeven_of_inputs (hRk1 : GGSecFiveRk1PhanInput) (hL1 : GGQTwoL1Input)
    (hGen : GGQTwoGenInput) (hOrth : GGQTwoCellInput qtwoOrthL)
    (hUnit : GGQTwoCellInput qtwoOrthL.compl) : GGSecFivePhanDQTwoSeven :=
  GGSecFivePhanDQTwoAt.of_cells
    (ggSecFivePhanDQTwoCell_of_inputs (R := fun m => 7 ≤ m) (fun _ hm => le_trans (by decide) hm)
      hRk1 hL1 hGen hOrth (ggQTwoFarInput_of_cell qtwoParabConj hOrth))
    (ggSecFivePhanDQTwoCell_of_inputs (R := fun m => 7 ≤ m) (fun _ hm => le_trans (by decide) hm)
      hRk1 hL1 hGen hUnit (ggQTwoFarInput_of_cell qtwoParabConj hUnit))

end Producer

end CFSG.StandardType.QTwo

end
