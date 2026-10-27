module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTableBTwDThreeLabel_of_rest3 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTableBRest3 GGTableBUnitaryLabel p lab) (hs : LargeEvenSplit p lab) :
    GGTableBTwDThreeLabel p lab :=
  ggTableBTwDThreeLabel_of_unitary h.1
    (fun hl => h.2 (by simp only [GGTableBDoneLabel3, hl, or_true])) hs

theorem ggBstarInputOn_rest3_unitary : GGBstarInputOn (GGTableBRest3 GGTableBUnitaryLabel) :=
  ggBstarInputOn_twDThree.mono_split fun _ _ h hs => ggTableBTwDThreeLabel_of_rest3 h hs

theorem ggStdSubPreInputOn_rest3_unitary :
    GGStdSubPreInputOn (GGTableBRest3 GGTableBUnitaryLabel) :=
  ggStdSubPreInputOn_twDThree.mono_split fun _ _ h hs => ggTableBTwDThreeLabel_of_rest3 h hs

end CFSG.StandardType
