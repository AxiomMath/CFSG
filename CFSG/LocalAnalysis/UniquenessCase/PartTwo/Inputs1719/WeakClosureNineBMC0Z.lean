module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

theorem z_inter : InterChk k0.qLit k1.qLit zLit = true := by decide +kernel

theorem z_nodup : zLit.Nodup := by decide +kernel

theorem z_length : zLit.length = 4 := by decide +kernel

theorem z_five : FiveChk tLit dLit zLit zFive.1 zFive.2.1 zFive.2.2.1 zFive.2.2.2.1 zFive.2.2.2.2 =
    true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0
