module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin

set_option maxRecDepth 100000

theorem k0_chk : KChk tLit k0 = true := by decide +kernel

theorem k0_enum : KEnumChk tLit k0 k0sT k0qT k0yT k0sB k0qB k0yB = true := by
  decide +kernel

theorem k1_chk : KChk tLit k1 = true := by decide +kernel

theorem k1_enum : KEnumChk tLit k1 k1sT k1qT k1yT k1sB k1qB k1yB = true := by
  decide +kernel

theorem k2_chk : KChk tLit k2 = true := by decide +kernel

theorem k2_enum : KEnumChk tLit k2 k2sT k2qT k2yT k2sB k2qB k2yB = true := by
  decide +kernel

theorem k3_chk : KChk tLit k3 = true := by decide +kernel

theorem k3_enum : KEnumChk tLit k3 k3sT k3qT k3yT k3sB k3qB k3yB = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3
