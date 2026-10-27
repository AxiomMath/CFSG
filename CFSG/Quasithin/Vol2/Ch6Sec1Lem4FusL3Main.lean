module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Red2b
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Inn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem kg614FusionL3_holds : KG614FusionL3 :=
  kg614FusionL3_of_locFusL3 fun _ _ _ hq h => locFusL3_inn hq h

theorem kg614Fusion_holds : KG614Fusion :=
  kg614Fusion_of kg614FusionL2_holds kg614FusionL3_holds

end CFSG.Quasithin.H13
