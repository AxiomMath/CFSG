module

public import CFSG.Quasithin.Vol2.Ch12Sec1Assembly
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1NmF
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Sch
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1A318
public import CFSG.Quasithin.Background.A318PFacts2
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.EmptyFaithful.R3c18WD4
public import CFSG.Quasithin.EmptyFaithful.T1515eE
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem6Insp
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9Odd
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11BorelC
public import CFSG.Quasithin.Vol2.KGFactLem1211Max
public import CFSG.Quasithin.Vol2.KGFactLem1211G2
public import CFSG.Quasithin.H13.NQCatSL3Sect
public import CFSG.Quasithin.H13.NQCatNNMod
public import CFSG.Quasithin.H13.NQCatG24Comp
public import CFSG.Quasithin.H13.VolIC129Holds
public import CFSG.Quasithin.EmptyFaithful.List115Native
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

theorem stmt12_1_11_of_remaining
    (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h443 : Stmt4_4_3Orbit') (hE : E2.E22StatementC)
    (h19 : ∀ (G : Type) [Group G] [Finite G], ASC19Statement G)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hInsp : Lem1211HeInsp) (hLin : Lem1211NormalLin) (hStep : Lem1214Step) : Stmt12_1_11 := by
  have h129 := VolI.asc129Statement_holds
  have h36 := Vol2Native.a36CoreForSQTKCat_proved
  have h37 := Vol2Native.a37ForSQTKCat_proved
  have h38 := C129Native.a38ForSQTKCat_proved
  have h39 := Vol2Native.a39ForSQTKCat_proved
  have hHe : Lem1211He := lem1211He_of h331 h37 h38 h39 lem1211HeSchreier_holds hInsp
  have hN : Lem1211Normal := lem1211Normal_of_inputs h331 h129 h19 hLin
    (lem1211NormalA318_of (a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds)
        VolI.a36ForSQTK_holds (a38ForSQTK_of_cat C129Native.a38ForSQTKCat_proved)
        l34NotL42Fact1515e_of_cert) KGAntiflag.lem1211NormalMax_holds
  have hNN : Lem1211NotNormal := lem1211NotNormal_of_inputs h331 h129 h36 h37 h38 h39 hC27
    B5.asB51_holds asA21SQTKSection NQCat.NNParab.lem1211NNParab_holds KGG2.lem1211NNG2_holds
    NQCat.SL3Sect.lem1211NNSL3_holds NQCat.NNMod.lem1211NNMod_holds
  have hComp : Lem1216Comp := lem1216Comp_of lemma115_3_List_native h37 h39
    (lem1216CompInsp_of NQCat.G24.lemCompG24_holds)
  have hH91 := lemH91_holds
  have h1211 := lem1211_of h1001 h331 hHe hN hNN
  have h1213 := lem1213_of h1001 h331 h1211 hH91 H9Lin.lemH92Use_holds H9Lin.lemH9FF5_holds
    H9Lin.lemH9Comm_holds
  have h1215 := lem1215_of h1001 h331 h1211 h1213 (lem1214_of h1001 h331 hStep) hH91
  have h1216 := lem1216_of h1001 h331 hH91 h1215
    (lem1216Gen_of h1001 h331 h1211 hH91 h1215 hComp)
  have h1217 := lem1217_of h1001 h331 h1211 hH91 h1213 h1216 H9Four.lemH93Use_holds
    H9Four.lemH9Rank4_holds H9Four.lemH9FF4_holds
  have h1218 := lem1218_of h1001 h331 h1211 hH91 h1216 h1217 H9Lin.lemH92Use_holds
    H9Four.lemH93Use_holds H9Four.lemH9Rank4_holds H9Lin.lemH9Cent_holds H9Lin.lemH9Axes_holds
  exact stmt12_1_11_of_open121 h1001 h331 h443 hE hHe hN hNN hStep hComp (lem12211Borel_of_e22 hE)
    (lem1219OddLocal_of h1001 h331 h1211 hH91 h1217 h1218 hE)

end CFSG.Quasithin.H13
