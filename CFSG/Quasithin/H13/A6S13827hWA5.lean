module

public import CFSG.Quasithin.H13.A6S13821zz36
public import CFSG.Quasithin.Background.C48OpenKW
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverFin
public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Gen
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Milestones.ASVolI.C41.BigStmt
public import CFSG.Quasithin.H13.A6S13827gWA5

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt13_8_1_of_root5fW_A5
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3) (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hcorr : CFSG.Quasithin.MS93.C134Weak)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (hKW : CFSG.Quasithin.KGJ4.J4TwoLocalsKW)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (hK : Input13721K) (h28 : Input13828Six)
    (hAut : Fact13820Aut)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat)
    (hG2 : Lem13827G2) : Stmt13_8_1 :=
  have hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z :=
    CFSG.Quasithin.H13.Ch4.gap437Sp4Z_of CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds
      (CFSG.Quasithin.H13.Ch4.lemmaC53C56Six_of CFSG.Quasithin.theoremC126_proved
        CFSG.Quasithin.C58NS.minParabolicBlockSubnormal_holds)
      CFSG.Quasithin.a37ForSQTK_proved CFSG.Quasithin.a38ForSQTK_proved
      CFSG.Quasithin.a39ForSQTK_proved
  have h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G := fun _ _ _ =>
    CFSG.Quasithin.C48.asc48Statement_of_kw
      (CFSG.Quasithin.C41Pf.burnsideC41w_asc41Statement_of_big
        (CFSG.Quasithin.asc27Statement_of_c132 hC132 _) hcorr.big)
      (CFSG.Quasithin.asc27Statement_of_c132 hC132 _) hKW
      CFSG.Quasithin.C48Cover.c48SporCoverFact_holds
  stmt13_8_1_of_root5eW_A5 h331 h1332 h1222 h12213 h13315 h523 hC132 hcorr hC137 hA5 h48 h13316 h1341
    hK h28 hAut
    (case13820bSL34U38_holds h1332 h1222
      (stmt13_3_14_of_root5W_A5 h331 h1332 h1222 h12213 h523 hC132 hcorr hC137 hA5 h48 hZ437) h13315)
    hHat6 hHatM22 hL32Hat hG2 hZ437

end CFSG.Quasithin.H13.A6

end
