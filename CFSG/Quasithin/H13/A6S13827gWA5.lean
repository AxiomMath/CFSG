module

public import CFSG.Quasithin.H13.A6S13827g
public import CFSG.Quasithin.MS93.C134CorrM
public import CFSG.Quasithin.H13.GoldschmidtU43ModCert
public import CFSG.Quasithin.Background.SmithC27Holds
public import CFSG.Quasithin.H13.A6S13827eWA5
public import CFSG.Quasithin.H13.A6S1515CTKHubs

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

theorem stmt13_3_14_of_root5W_A5
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h523 : CFSG.Quasithin.H13.Stmt5_2_3)
    (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32) (hcorr : CFSG.Quasithin.MS93.C134Weak)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G)
    (hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z) : Stmt13_3_14 :=
  U3.stmt13_3_14_of_open (h_Stmt3_3_1 := h331) (h_Stmt12_2_2 := h1222)
    (h_Stmt12_2_13 := h12213) (h_Stmt13_3_2 := h1332)
    (h_C137StatementFiveSQTK := hC137) (h_Stmt5_2_3 := h523)
    (h_Res1328a := A5.res1328a_of_c48W_A5 (h_Stmt3_3_1 := h331)
      (h_Stmt13_3_2 := h1332) (h_AS_C_1_34_corr := hcorr.big) (h_F112SliceA5 := hA5)
      (h_ASC48Statement_G := h48) (h_Gap437Sp4Z := hZ437))
    (h_Rest1327 := A5.rest1327_of_c48W (h_Stmt3_3_1 := h331) (h_Stmt12_2_2 := h1222)
      (h_Stmt13_3_2 := h1332) (h_AS_C_1_34_corr := hcorr.big) (h_ASC48Statement_G := h48)
      (h_Gap437Sp4Z := hZ437))
    (h_U3LineComponentExclusion := U3.u3LineComponentExclusion_of_c27W h1332
      (asc27Statement_of_c132 hC132) hcorr.small hcorr.big)

theorem stmt13_8_1_of_root5eW_A5
    (h331 : CFSG.Quasithin.H13.Stmt3_3_1) (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2)
    (h12213 : CFSG.Quasithin.H13.Stmt12_2_13) (h13315 : Stmt13_3_15)
    (h523 : CFSG.Quasithin.H13.Stmt5_2_3) (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hcorr : CFSG.Quasithin.MS93.C134Weak)
    (hC137 : CFSG.Quasithin.H13.U3.GC137.C137StatementFiveSQTK)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (h48 : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (hK : Input13721K) (h28 : Input13828Six)
    (hAut : Fact13820Aut) (hb : Case13820bSL34U38)
    (hHat6 : Case13821Hat6) (hHatM22 : Case13821HatM22) (hL32Hat : Case13821L32Hat)
    (hG2 : Lem13827G2) (hZ437 : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z) : Stmt13_8_1 :=
  stmt13_8_1_of_root5cW_A5 h331 h1332 h1222 h12213 h13315 h523 hC137 hcorr.small hcorr.big hA5 h48
      (asc27Statement_of_c132 hC132) h13316 h1341 (input13515CTK_of_hubs h1222 h13315)
      U43.stmtU43Type hK h28 hAut
      (case13820a_holds h1332 h1222
          (stmt13_3_14_of_root5W_A5 h331 h1332 h1222 h12213 h523 hC132 hcorr hC137 hA5 h48 hZ437)
          h13315) hb hHat6 hHatM22 hL32Hat hG2 hZ437

end CFSG.Quasithin.H13.A6

end
