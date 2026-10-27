module

public import CFSG.RankThree.PartTwo.Census.Sporadic.Common
public import CFSG.RankThree.PartTwo.Census.Sporadic.J4Bridge
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint

theorem excluded433_J4 : Excluded433 (.sporadic .J4) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hc, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
  exact @excluded433_sporadic_of_cubic .J4 NativeSporadic.J4 Units.instGroup
    (fun h => @nonempty_mulEquiv_carrier_J4 h) _ CFSG.Sporadic.J4.card_J4 (by norm_num)
    ⟨x, y, hxy, hc⟩

end CFSG.RankThree.PartTwo.Census
