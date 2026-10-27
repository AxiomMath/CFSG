module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Omega

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Sec2Omega
open MulAction

abbrev OmG := ↥(CFSG.Open.timmesfeldOmega qMinus)

theorem Om_nonsing_ncard : {v : Fin 6 → ZMod 2 | qMinus v = 1}.ncard = 36 := by
  have e : {v : Fin 6 → ZMod 2 | qMinus v = 1} =
      ↑(Finset.univ.filter fun v : Fin 6 → ZMod 2 => qMinus v = 1) := by
    ext v
    simp
  rw [e, Set.ncard_coe_finset]
  decide

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
