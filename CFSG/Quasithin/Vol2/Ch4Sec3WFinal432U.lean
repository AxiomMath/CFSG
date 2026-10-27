module

public import CFSG.Quasithin.Vol2.Ch4Sec3Final432
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Cfg
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Holds
public import CFSG.Quasithin.Vol2.KGFactKGU35
public import CFSG.Quasithin.Vol2.Ch4Sec3WL4316

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt4_3_2_of_inputs_l4316W
    (hR : L2RankOneSylowFact) (h126 : TheoremC126) (hMPB : C58NS.MinParabolicBlockSubnormal)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hG2 : Insp436G2) (hD4 : Insp436D4) (hF4 : Insp436F4) (hM2223 : Insp436M22M23)
    (hMult : Sp4MultTrivial)
    (hF : A318Facts) (h56 : AsB56) (hB414 : LemmaB414Corrected)
    (h312 : A312ForSQTK) (h134 : MS93.burnsideC134w_AS_C_1_34_corrBig) (hI : Insp4316)
    (hZ : Gap437Sp4Z) :
    Stmt4_3_2 := by
  have h135 : AsC135Three := asC135Three_holds
  have hC : LemmaC53C56Six := lemmaC53C56Six_of h126 hMPB
  have h36 : A36ForSQTK := CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved
  have h122 : Lemma122A := fun G _ _ hS hQ hna H L hH hL p hp hp2 hc hd =>
    Vol2Native.lemma122A_proved G hS hna (qtkeCore_of_cat hna hQ) H L hH hL p hp hp2 hc hd
  exact stmt4_3_2_of_inputs hR h126 hMPB hC48 hG2 hD4 hF4 hM2223 hMult hF h56
    (lemma43Upto_ofW h135 hR hC h36 h37 h38 h39 h312 h134 h122 hF hI
      (step43L34_of hB414 h135 hR hC h36 h37 h38 h39)
      (step43U35_of KGU35.kgu35_holds h135 hR hC h36 h37 h38 h39)) hB414 hZ

end CFSG.Quasithin.H13.Ch4
