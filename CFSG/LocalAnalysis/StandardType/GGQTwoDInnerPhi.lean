module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

theorem ggQ2_D_inner_phi (n : ℕ) (hn : 5 ≤ n) :
    GGQ2QuandleInner (ggBCReflSet (ggDRoots n)) (ggBCW n) := by
  intro π hT hinj hπ
  exact ggQ2_quandle_aut_D n hn π hT hinj hπ

end CFSG.StandardType

end
