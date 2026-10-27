module

public import CFSG.Quasithin.Background.E6EighteenHeCtx
public import CFSG.Quasithin.Background.E6EighteenJ
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.Vol2.GoldschmidtC58NSProved
public import CFSG.Quasithin.Background.VolII31Three
public import CFSG.Quasithin.H13.A5Close1321c
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.H13.NQCatE68Borel
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.Background.E6NineteenF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporMain
public import CFSG.Quasithin.Background.E6TwentyThreeI
public import CFSG.Quasithin.H13.KGFactE623A5
public import CFSG.Quasithin.H13.KGFactE623Sp4Cent
public import CFSG.Quasithin.Background.ONanE68Holds
public import CFSG.Quasithin.Background.E6Twenty
public import CFSG.Quasithin.Background.E6TwentyFiveH
public import CFSG.Quasithin.Background.E6TwentyFiveJ

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

theorem e618Stmt_of_heResidual
    (hRes : E618HeResidual) : E618Stmt :=
  e618Stmt_of_heCtx
    (theorem311_of_solvable_nonsolvable
      (EmptyFaithfulMultiple.input311Solvable_of (G64.inputC512G64_of_lemmaG64
        (G64.lemmaG64_of_b5 asB56_holds))) C58NS.theorem311Nonsolvable_proved)
    Ch1.lemma115_3_List_proved
    (VolI.as_I_3_1_three_of Vol2Native.a36CoreForSQTKCat_proved H13.A5.a38ForSQTKCat_holds)
    e618A7Facts_holds noA7FixL115NotHe_holds E68Proof.e68Stmt_holds hRes

theorem e625Stmt_of_open_heRes
    (h104 : Asc81c.Thm104) (hRes : E618HeResidual) : E625Stmt := by
  have h68 : E68Stmt := E68Proof.e68Stmt_holds
  have h311 : Theorem311Stmt := theorem311_of_solvable_nonsolvable
    (EmptyFaithfulMultiple.input311Solvable_of (G64.inputC512G64_of_lemmaG64
      (G64.lemmaG64_of_b5 asB56_holds))) C58NS.theorem311Nonsolvable_proved
  have hlist : Lemma115_3_List := Ch1.lemma115_3_List_proved
  have hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G :=
    H13.VolI.asc129Statement_holds
  have h621 : E621Stmt :=
    e621_of (e620_of h311 (e619_of h311 hlist (e618Stmt_of_heResidual hRes) e619Insp_holds))
  exact e625_of_rest (e624_of h104) (e611Strong_of h68 hC129 H13.NQCat.e68BorelKernel_holds)
    (e625NotTwo_of_rest hlist h621 Spor.e68CentComp_holds
      (e625NotTwoBlock_of h68 (e625NotTwoBlockNQ_of H13.VolI.a36ForSQTK_holds
        Vol2Native.a37ForSQTKCat_proved H13.A5.a38ForSQTKCat_holds h621 hC129) h621
        Vol2Native.a37ForSQTKCat_proved Vol2Native.a39ForSQTKCat_proved))

theorem as_E_6_3_of_open_heRes
    (h104 : Asc81c.Thm104) (hRes : E618HeResidual) (hLay : E623A3Layer) :
    ASInputs.AS_E_6_3 := by
  have h68 : E68Stmt := E68Proof.e68Stmt_holds
  have h311 : Theorem311Stmt := theorem311_of_solvable_nonsolvable
    (EmptyFaithfulMultiple.input311Solvable_of (G64.inputC512G64_of_lemmaG64
      (G64.lemmaG64_of_b5 asB56_holds))) C58NS.theorem311Nonsolvable_proved
  have hlist : Lemma115_3_List := Ch1.lemma115_3_List_proved
  have hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G :=
    H13.VolI.asc129Statement_holds
  have h618 : E618Stmt := e618Stmt_of_heResidual hRes
  have h621 : E621Stmt := e621_of (e620_of h311 (e619_of h311 hlist h618 e619Insp_holds))
  have h622 : E622Stmt := e622_of h311 hlist h618 h621 Spor.e68CentComp_holds
  have h623 : E623Stmt := e623_of_kg h311 h622 H13.VolI.a36ForSQTK_holds
    Vol2Native.a37ForSQTKCat_proved H13.A5.a38ForSQTKCat_holds Vol2Native.a39ForSQTKCat_proved
    h621 h68 (H13.KGE623.e623CentA5Block_of H13.KGE623.sp44OrderThreeCent_holds) hC129
    (e623A3Dichotomy_of_layer h311 hC129 h621 hLay)
  exact as_E_6_3_of h311 h623 (e625Stmt_of_open_heRes h104 hRes)

end E6

end CFSG.Quasithin
