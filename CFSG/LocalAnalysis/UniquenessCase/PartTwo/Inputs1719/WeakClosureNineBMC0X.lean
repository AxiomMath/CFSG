module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

theorem k2_chk : KChk tLit k2 = true := by decide +kernel

theorem k2_enum : KEnumChk tLit k2 k2sT k2qT k2yT k2sB k2qB k2yB = true := by
  decide +kernel

theorem k2_o2 : O2Chk k2 k2o2 = true := by decide +kernel

theorem k3_chk : KChk tLit k3 = true := by decide +kernel

theorem k3_enum : KEnumChk tLit k3 k3sT k3qT k3yT k3sB k3qB k3yB = true := by
  decide +kernel

theorem k3_o2 : O2Chk k3 k3o2 = true := by decide +kernel

theorem k4_chk : KChk tLit k4 = true := by decide +kernel

theorem k4_enum : KEnumChk tLit k4 k4sT k4qT k4yT k4sB k4qB k4yB = true := by
  decide +kernel

theorem k4_o2 : O2Chk k4 k4o2 = true := by decide +kernel

theorem k5_chk : KChk tLit k5 = true := by decide +kernel

theorem k5_enum : KEnumChk tLit k5 k5sT k5qT k5yT k5sB k5qB k5yB = true := by
  decide +kernel

theorem k5_o2 : O2Chk k5 k5o2 = true := by decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0
