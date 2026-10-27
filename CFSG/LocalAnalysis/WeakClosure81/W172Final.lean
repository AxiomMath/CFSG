module

public import CFSG.LocalAnalysis.WeakClosure81.W172Lem26
public import CFSG.LocalAnalysis.WeakClosure81.W172Main

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w3Thm172Weak_of_thm162 (h162 : W3Thm162Gt2 G) : W3Thm172Weak G :=
  w3Thm172Weak_of_no_minCex fun _ _ _ _ c =>
    c.w172_false h162 (w172_lem26 h162 c.hyp.setting c.hyp.ne_bot c.mbar)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
