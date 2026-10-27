module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreDefs
import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
import CFSG.LocalAnalysis.StandardType.GGF4OrigRep

public section

namespace CFSG.StandardType

open CFSG.StandardType.F4Model

theorem ggF4B3Core_holds : GGF4B3Core := by
  intro W _ cs a ha o01 o12 o02
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  obtain ⟨H, hne, haH, hd⟩ :=
    R.core_of_rep (a := a) (fun i => (F4Rep.isRefl_iff hRs).2 (ha i)) o01 o12 o02
  exact ⟨H, hne, haH, fun t ht => hd t ((F4Rep.isRefl_iff hRs).2 ht)⟩

end CFSG.StandardType

end
