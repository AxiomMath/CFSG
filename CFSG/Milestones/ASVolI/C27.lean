module

public import CFSG.Milestones.ASVolI.C2ChiBlocks
public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc

public section

namespace CFSG.ASVolI

section C27

set_option linter.unusedSectionVars false


theorem as_C_2_7
    : C_2_7 :=
  burnsideC2h_c27_of_desc CFSG.Quasithin.MS93.S4L.burnsideSp4H_s34RDescSp4

end C27

end CFSG.ASVolI
