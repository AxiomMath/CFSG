module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.F1Models
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

noncomputable def oTwoQuotCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    oTwoQuot X ≃* oTwoQuot Y :=
  QuotientGroup.congr (CFSG.Open.pCore 2 X) (CFSG.Open.pCore 2 Y) e (by
    exact CFSG.pCore_map_iso 2 e)

end CFSG.Quasithin.H13
