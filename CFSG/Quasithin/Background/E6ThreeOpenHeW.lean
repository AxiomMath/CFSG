module

public import CFSG.Quasithin.Background.E6EighteenHeInv
public import CFSG.Quasithin.Background.E6EighteenHeResG
public import CFSG.Quasithin.Background.E6ThreeOpenHeRes
public import CFSG.Quasithin.Background.E6TwentyThreeN
public import CFSG.Quasithin.H13.KGFactE623A3

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

theorem e618HeResidual_holds :
    E618HeResidual :=
  e618HeResidual_of_invPerfect factHeInvPerfect_holds

theorem e618Stmt_holds :
    E618Stmt :=
  e618Stmt_of_heResidual e618HeResidual_holds

theorem as_E_6_3_of_thm104
    (h104 : Asc81c.Thm104) (hLay : E623A3Layer) : ASInputs.AS_E_6_3 :=
  as_E_6_3_of_open_heRes h104 e618HeResidual_holds hLay

theorem as_E_6_3_of_thm104_over
    (h104 : Asc81c.Thm104) (hOver : E623A6Over) :
    ASInputs.AS_E_6_3 := by
  have h311 : Theorem311Stmt := theorem311_of_solvable_nonsolvable
    (EmptyFaithfulMultiple.input311Solvable_of (G64.inputC512G64_of_lemmaG64
      (G64.lemmaG64_of_b5 asB56_holds))) C58NS.theorem311Nonsolvable_proved
  have hlist : Lemma115_3_List := Ch1.lemma115_3_List_proved
  have hI31 : AS_I_3_1_three :=
    VolI.as_I_3_1_three_of Vol2Native.a36CoreForSQTKCat_proved H13.A5.a38ForSQTKCat_holds
  have h618 : E618Stmt := e618Stmt_holds
  have h621 : E621Stmt := e621_of (e620_of h311 (e619_of h311 hlist h618 e619Insp_holds))
  have h622 : E622Stmt := e622_of h311 hlist h618 h621 Spor.e68CentComp_holds
  exact as_E_6_3_of_thm104 h104 (e623A3Layer_of h311 h618 h621 h622 E68Proof.e68Stmt_holds
    H13.KGE623A3.e623CentA3Comp_holds
    (e623A6Config_of_detour h311 (e623A6Detour_of_over h311 hI31 hOver)))

end E6

end CFSG.Quasithin
