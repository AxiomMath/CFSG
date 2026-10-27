module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Y143Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open CFSG CFSG.RankThree.PartTwo

theorem k143Excl_of_l143NoConfig (hN : L143NoConfig) : K143Excl :=
  fun _ _ _ hY hq hZ _ ⟨hx3, hxZ, hc, hf⟩ => hN.false_of_point hY hq hZ hx3 hxZ hc hf

theorem k143Excl_of (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hin : Sec4.Census.CoverInputs46) (heig : L143EigProp) (hK : L143RowsK) : K143Excl :=
  k143Excl_of_l143NoConfig (l143NoConfig_of h2 h43 hin heig hK)

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
