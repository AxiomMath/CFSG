module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD0

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts

set_option maxRecDepth 100000

theorem subs1_chk : SubsChk k1.qLit subs1 idx1 = true := by decide +kernel

theorem q1_length : k1.qLit.length = 16 := by decide +kernel

theorem stats1_chk : ∀ k < subs1.length,
    CStatChk tLit dLit ks [0, 1] subs1 stats1 (subs1.getD k []) (stats1.getD k (.k761 0)) = true := by
  decide +kernel

theorem qstat1_chk : CStatChk tLit dLit ks [0, 1] subs1 stats1 k1.qLit qstat1 = true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0
