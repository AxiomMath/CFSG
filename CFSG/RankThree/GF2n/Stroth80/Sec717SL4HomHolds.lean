module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
import CFSG.RankThree.PartOne.K159.KleinNoInvForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sl4NoInvForm_holds : SL4NoInvFormStatement := by
  intro K _ _ _ hK σ β hβ
  exact PartOne.K159.Klein.noInvForm_eq_zero hK (σ : K →+* K) β hβ

end CFSG.RankThree.GF2n.Stroth80
