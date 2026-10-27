module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M1

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin

set_option maxRecDepth 100000

theorem k0_chk : KChk tLit k0 = true := by decide +kernel

theorem k0_enum : KEnumChk tLit k0 k0sT k0qT k0yT k0sB k0qB k0yB = true := by
  decide +kernel

theorem k1_chk : KChk tLit k1 = true := by decide +kernel

theorem k1_enum : KEnumChk tLit k1 k1sT k1qT k1yT k1sB k1qB k1yB = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M1
