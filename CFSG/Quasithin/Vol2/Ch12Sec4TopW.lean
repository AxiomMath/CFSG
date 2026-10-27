module

public import CFSG.Quasithin.Vol2.Ch12Sec4Wired
public import CFSG.Quasithin.Vol2.Ch12Sec4C8Char
public import CFSG.Quasithin.Vol2.Ch12Sec4C8KG
public import CFSG.Quasithin.Vol2.Ch12Sec4C8L2p
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma4
public import CFSG.Quasithin.Vol2.Ch12Sec4MParam
public import CFSG.Quasithin.Background.VolII31Holds
public import CFSG.Quasithin.Vol2.Ch12Sec4N6FinW

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt12_4_2_of_inputsW
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) (h3228 : Stmt3_2_2_eight)
    (h1227 : Stmt12_2_7) (h1232 : Cor12_3_2) (h1229 : Stmt12_2_9)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h42 : AsB42)
    (h51 : AsB51) (h63 : ASInputs.AS_E_6_3) (hMS : C134L32CorrM)
    (hSL : BlockQ1246SL27) (hG2 : G2MParamFact1244) (h68 : E6.E68Stmt)
    (hlist : Lemma115_3_List) (hF318 : A318Facts) (hKF : KnownFacts15122Types)
    (hP3 : E6.E619Insp) (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) :
    Stmt12_4_2 := by
  have hpre := pre1242_of_stmts h331 h1222
  have h12210 := stmt12_2_10_of_1222 h1222
  have h1241 := lemma12_4_1_of h331 h1222 h3228 h1227 h1232
  exact stmt12_4_2_of_lemmas h1241 (lemma12_4_3_one_of_pre hpre)
    (lemma12_4_4_of h331 h1222 h323 hpre h3228 h1229 h12210 h1241 h42 h63)
    (post1244_of h331 h1222 hpre (mParam1244_of h331 h1222 hpre h12210 hG2))
    (lemma12_4_8_of_inputs h331 h1222 h323 h3228 hpre h1229 h68 hlist hF318 h36 h38 hKF hP3
        l32ListFact1248 l33ExclusionFact hatA67Fact1248 l2pThreeFact1248 l2pEmbedFact1248
        AS_I_3_1_one_two_holds hC129)
    (lemma12_4_9_of_stmts h331 h1222 hpre h12210 (lemma12_4_7_of_stmts h331 h1222 hpre
      (lemma12_4_6_of_inputsW h331 h1222 hpre h3228 h1229 h51 h37 h38 h39 h12210 hMS hSL)))

end CFSG.Quasithin.H13
