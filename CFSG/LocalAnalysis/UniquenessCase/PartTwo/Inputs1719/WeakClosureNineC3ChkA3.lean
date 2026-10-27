module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3DataA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C.A

open CFSG.LocalAnalysis.WeakClosure81.NFA6.Core CFSG.LocalAnalysis.WeakClosure81.ChkN

set_option maxRecDepth 100000

theorem ent_ok_0 : entOkN 46 MD En0 = true := by decide +kernel
theorem ent_ok_1 : entOkN 46 MD En1 = true := by decide +kernel
theorem ent_ok_2 : entOkN 46 MD En2 = true := by decide +kernel
theorem ent_ok_3 : entOkN 46 MD En3 = true := by decide +kernel
theorem ent_ok_4 : entOkN 46 MD En4 = true := by decide +kernel
theorem ent_ok_5 : entOkN 46 MD En5 = true := by decide +kernel
theorem ent_ok_6 : entOkN 46 MD En6 = true := by decide +kernel
theorem ent_ok_7 : entOkN 46 MD En7 = true := by decide +kernel
theorem ent_ok_8 : entOkN 46 MD En8 = true := by decide +kernel
theorem ent_ok_9 : entOkN 46 MD En9 = true := by decide +kernel
theorem ent_ok_10 : entOkN 46 MD En10 = true := by decide +kernel
theorem ent_ok_11 : entOkN 46 MD En11 = true := by decide +kernel
theorem ent_ok_12 : entOkN 46 MD En12 = true := by decide +kernel
theorem ent_ok_13 : entOkN 46 MD En13 = true := by decide +kernel
theorem ent_ok_14 : entOkN 46 MD En14 = true := by decide +kernel
theorem ent_ok_15 : entOkN 46 MD En15 = true := by decide +kernel

theorem inv_ok : invCheckN 46 MD.T MD.Tinv = true := by decide +kernel

theorem seed_ok : seedOkN 46 MD = true := by decide +kernel

theorem bot_ok : botOkN 46 MD = true := by decide +kernel

theorem sq_ok : sqOkN 46 MD = true := by decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NF3C.A
