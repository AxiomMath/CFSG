module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18c
public import CFSG.Quasithin.Vol2.Ch12Sec6L18BL
public import CFSG.Quasithin.Vol2.Ch12Sec6L18M2
public import CFSG.Quasithin.Vol2.Ch12Sec6L18Kw
public import CFSG.Quasithin.Vol2.KGFact12617a
public import CFSG.Quasithin.Vol2.KGFact12617d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem lemma12_6_17_of_inputs (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (h56 : AsB56) (h51 : AsB51)
    (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15)
    (hD10 : Lemma12_6_16) (hLie7 : FactKv12617LieFam) (hL527 : FactKv12617L52) :
    Lemma12_6_17 :=
  lemma12_6_17_of h1222 h36 h56 hD2 hD5 hD7 hD9 hD10 (KG12618.factKv12617_of hLie7 hL527
      KG12618.factKv12617A8_holds)
    (factUv12617_of (factUv12618_of h1222 h36 h51 hD7 hD9))

theorem final1262_of_inputs (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat) (h56 : AsB56) (h51 : AsB51)
    (hD2 : Lemma12_6_4_5) (hD5 : Lemma12_6_11) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15)
    (hD10 : Lemma12_6_16) (hLie7 : FactKv12617LieFam) (hL527 : FactKv12617L52)
    (hLie8 : FactKv12618LieFam) (hL528 : FactKv12618L52) : Final1262 :=
  final1262_of_facts h331 h1222 h36 h56 hD2 hD5 hD7 hD9 hD10
    (lemma12_6_17_of_inputs h1222 h36 h56 h51 hD2 hD5 hD7 hD9 hD10 hLie7 hL527)
    (blockL12618_of h331 h1222 hD2) (KG12618.factKv12618_of hLie8 hL528)
    (factUv12618_of h1222 h36 h51 hD7 hD9) (blockKv12618_of h51 h1222 h36 hD2 hD7 hD9)

end CFSG.Quasithin.H13
