module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin

set_option maxRecDepth 100000

theorem reps_chk : RepsChk tLit t0Lit ks reps = true := by decide +kernel

theorem pairs_chk : PairsChk tLit reps pairs = true := by decide +kernel

theorem conj_chk : ConjRepChk tLit pairs cwr = true := by decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3
