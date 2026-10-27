module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4310
public import CFSG.Quasithin.Vol2.Ch4Sec3L439

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt4_3_2_of_steps (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h436 : Lemma436Comp) (hSp4 : Lemma437Sp4) (hA7 : Lemma437A7) (hKG : SL3ParabolicAutFact)
    (h439 : Lemma439Fix) (h4310 : Lemma4310Two) (hEnd : Lemma43End) : Stmt4_3_2 :=
  stmt4_3_2_of hR hC (core432_of hR hC hC48 inspC48L2_holds h36 h37 h38 h39 h436 hSp4 hA7
    (lemma437SL3_holds hR hC h37 h38 h39 hKG) (lemma439_of h439)
    (lemma4310_of h4310 hR hC h37 h38 h39) hEnd)

end CFSG.Quasithin.H13.Ch4
