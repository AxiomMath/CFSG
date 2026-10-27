module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

theorem subs0_chk : SubsChk k0.qLit subs0 idx0 = true := by decide +kernel

theorem q0_length : k0.qLit.length = 16 := by decide +kernel

theorem stats0_chk : ∀ k < subs0.length,
    CStatChk tLit dLit ks [0, 1] subs0 stats0 (subs0.getD k []) (stats0.getD k (.k761 0)) = true := by
  decide +kernel

theorem qstat0_chk : CStatChk tLit dLit ks [0, 1] subs0 stats0 k0.qLit qstat0 = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0
