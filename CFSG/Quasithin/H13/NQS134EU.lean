module

public import CFSG.Quasithin.H13.NQS134ET
public import CFSG.Quasithin.H13.NQS13412H
public import CFSG.Quasithin.H13.NQS134EN
public import CFSG.Quasithin.H13.NQS134ER

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

theorem stmtEnd134_of (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347One : U3.Stmt13_4_7One)
    (h1347 : U3.Stmt13_4_7L2) (h1348 : U3.Stmt13_4_8)
    (h1345 : Stmt13_4_5) (h1346 : Stmt13_4_6) (h331 : Stmt3_3_1) : StmtEnd134 := by
  intro G _ _ T L V z N
  have huniq := (stmt13_4_12_of hC137 h1332 h1228 hC58 h317 h56 h1222 h1347One h1347 h1348
    h1345 h1346 G T L V z N).1.2.2
  have hz := N.zV1
  have hzL := N.zL
  have hHz := N.inHz h1332 hC58 h317 h56
  obtain ⟨⟨K, hK⟩, -⟩ := h1346 G T L V N.S z _ hz hzL hHz N.nsolv
  obtain ⟨W, _, D⟩ := exists_data13410 h1345 h1346 N.S hz hzL hHz N.nsolv hK
  have hnhat := D.not_hat hC137 h1332 h1228 hC58 h317 h56
  have he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨h5, -, -, -⟩ := h1332 G T L N.S.h13 L N.S.h13.faithful
    exact (U3.a6_or_hatA6_of_isA6On N.S.frame.L_le (U3.s134_pCoreOf_L_le N.S) h5
      (U3.s134_isA6On N.S)).resolve_right hnhat
  obtain ⟨hM, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  obtain ⟨-, -, hZW, hL1, hcZ, htype⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 N.S D.exists_inH
  have hA6 : quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)) :=
    (quasithinO2QuotientIso_iff L _).2 he
  have hCMT := U3.s134_CMV_le_T N.S (U3.s134_isPGroup_CMV N.S hA6 hM) h1222
  rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, ⟨h6, hWK⟩ | ⟨hW5, hc2, hc⟩⟩
  · exact D.false_l32 h331 h1222 hM hZV1 hL1Z hL1 hZW hcZ hK3 hnat hCMT huniq
  · exact D.false_nat h331 h1222 h1332 hM hZV1 hL1Z hL1 hZW hcZ hK6 h6 hWK hCMT huniq
  · exact D.false_core h331 h1222 h1332 hM hZV1 hL1Z hL1 hZW hcZ hK6 hW5 hc2 hc hCMT huniq

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

end CFSG.Quasithin.H13.NQS134
