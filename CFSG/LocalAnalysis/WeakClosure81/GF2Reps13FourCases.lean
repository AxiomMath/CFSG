module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13SwapMain
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4Main

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem w4Lem13_4_of (hGA : GriessAllModelsStatement) : W4Lem13_4 := by
  intro W _ _ hW Y _ hO t ht ht2 hrk K hK hmove
  rcases w16f_diag_dichotomy hW hK ht ht2 hrk hmove with htr | ⟨hnt, hrk3, f, hf⟩
  · exact w16f_case_one_swap hW hO hK ht ht2 hrk hmove htr
  · exact w16f_case_two hW hO hK ht ht2 hrk hrk3 hmove (w16f_isL3_of_surj hGA hO hK f hf) hnt

end CFSG.LocalAnalysis.WeakClosure81
