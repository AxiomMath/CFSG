module

public import CFSG.Quasithin.Vol2.Ch4Sec3C64
public import CFSG.Quasithin.Vol2.Ch4Sec3C53
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4Rank
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspRed
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspFFG2BT
public import CFSG.Quasithin.Vol2.Ch4Sec3L43Q517
public import CFSG.Quasithin.Vol2.Ch4Sec3C136
public import CFSG.Quasithin.Vol2.KGFactSL3
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt4_3_2_of_inputs
    (hR : L2RankOneSylowFact) (h126 : TheoremC126) (hMPB : C58NS.MinParabolicBlockSubnormal)
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (hG2 : Insp436G2) (hD4 : Insp436D4) (hF4 : Insp436F4) (hM2223 : Insp436M22M23)
    (hMult : Sp4MultTrivial)
    (hF : A318Facts) (h56 : AsB56)
    (hUpto : Lemma43Upto) (hB414 : LemmaB414Corrected) (hZ : Gap437Sp4Z) : Stmt4_3_2 := by
  have hC : LemmaC53C56Six := lemmaC53C56Six_of h126 hMPB
  have hInsp : Insp436Sp4 := insp436Sp4_of hG2 hD4 hF4 hM2223
  have hFF : InspFF436 := inspFF436_holds
  have h36 : A36ForSQTK := CFSG.Quasithin.H13.VolI.a36ForSQTK_holds
  have h37 : A37ForSQTK := a37ForSQTK_of_cat Vol2Native.a37ForSQTKCat_proved
  have h38 : A38ForSQTK := a38ForSQTK_of_cat
    (Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact Vol2Native.a134SQTKFactCat
      Vol2Native.a36CoreForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved)
  have h39 : A39ForSQTK := a39ForSQTK_of_cat Vol2Native.a39ForSQTKCat_proved
  have h122 : Lemma122A := fun G _ _ hS hQ hna H L hH hL p hp hp2 hc hd =>
    Vol2Native.lemma122A_proved G hS hna (qtkeCore_of_cat hna hQ) H L hH hL p hp hp2 hc hd
  have hStep : Step436Sp4 :=
    step436Sp4_of h36 h37 h38 h122 hF h56 hFF (step436KZ_holds h37 h39)
  exact stmt4_3_2_of_steps'' hR hC hC48 h36 h37 h38 h39
    (lemma436Comp_of hR hC h36 h37 h38 h39 hInsp
      (lemma436Sp4_of h37 h38 h39 hMult sp4ParabolicFacts_holds hStep))
    sl3ParabolicAutFact_holds lemmaC136_holds
    lemmaC64Ten_holds
    (lemma43End_of_b414 hUpto hB414) hZ

end CFSG.Quasithin.H13.Ch4
