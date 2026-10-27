module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieAll
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Fin

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126

theorem lemma12_6_31_of_certs
    (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (h1229 : Lemma12_6_29) (h1230 : Lemma12_6_30)
    (hK : KList12631) : Lemma12_6_31 :=
  lemma12_6_31_of l34LieFacts12631 h1222 h1228 h1229 h1230 hK

theorem kList12631_of_certs
    (h1229 : Lemma12_6_29) (h1230 : Lemma12_6_30) (hweak : KListWeak12631) : KList12631 :=
  kList12631_of l34LieFacts12631 h1229 h1230 hweak

end CFSG.Quasithin.H13
