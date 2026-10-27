module

public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch8Sec1M24
public import CFSG.Quasithin.Background.HMathieuFacts
public import CFSG.Quasithin.Vol2.Ch8Sec1Prop
public import CFSG.Quasithin.Vol2.Ch8Assembly
public import CFSG.Quasithin.Vol2.Ch8Sec3InputZ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3

theorem input8_3_Q_proved :
    Input8_3_Q := fun G _ _ T L I hyp => (stmt3_2_2_eight_proved G T L I hyp.fsu).2.2.symm

theorem input7_0_2_unique_proved :
    Input7_0_2_unique := by
  intro G _ _ T L I hyp
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hU := lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian a37ForSQTK_proved
    a38ForSQTK_proved a39ForSQTK_proved hyp.fsu.sylow hyp.fsu.maximal
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  have hLTQ : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef, ← (h3228 G T L I hyp.fsu).2.2]
    exact (sup_le_sup_right (le_fsuL0 T L) T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hVQ : fsuV T I ≤ Q := fun v hv =>
    ⟨fsuV_le_T hyp.fsu hV hN hv, Subgroup.mem_centralizer_iff.2 fun w hw =>
      congrArg Subtype.val (hV.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)⟩
  have hQ1 : Q ≠ ⊥ := fun h => fsuV_ne_bot hyp.fsu (le_bot_iff.1 (h ▸ hVQ))
  have hQ2 : IsPGroup 2 Q := hyp.fsu.sylow.1.to_le inf_le_left
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (⟨Q, hQ1, hQ2, rfl⟩ :
    IsTwoLocal (Subgroup.normalizer (Q : Set G)))
  have hM'eq : M' = fsuM T L := hU.2 M' ⟨hM', hLTQ.trans hle⟩
  exact ⟨⟨hU.1.1, hM'eq ▸ hle⟩, fun M'' hM'' => hU.2 M'' ⟨hM''.1, hLTQ.trans hM''.2⟩⟩

theorem stmt8_1_1_final_q
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h711 : Stmt7_1_1_normal)
    (h325 : Stmt3_2_5) : Stmt8_1_1 :=
  stmt8_1_1_of hC48 a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved
    (stmtFSUModule_of_eight stmt3_2_2_eight_proved) h711 h325 input8_3_Q_proved
    input7_0_2_unique_proved

theorem stmt8_1_2_final_q
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h711 : Stmt7_1_1_normal)
    (h325 : Stmt3_2_5) (hin : Input8_1_2) : Stmt8_1_2 :=
  stmt8_1_2_of a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved
    (stmtFSUModule_of_eight stmt3_2_2_eight_proved) h711 h325 (stmt8_1_1_final_q hC48 h711 h325) hin
    H.Mathieu.stmtH13Card H.Mathieu.stmtH15O2

theorem stmt8_1_3_final_q
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h711 : Stmt7_1_1_normal)
    (h325 : Stmt3_2_5) (hin : Input8_1_2) (h734 : Stmt7_3_4) : Stmt8_1_3 :=
  stmt8_1_3_of a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved
    (stmtFSUModule_of_eight stmt3_2_2_eight_proved) (stmt8_1_2_final_q hC48 h711 h325 hin) h734
    H.Mathieu.stmtH13Card H.Mathieu.stmtH14PRank H.Mathieu.stmtH15M22 H.Mathieu.stmtH15M24

theorem stmt8_1_3_M24_final_q
    (hC48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G) (h711 : Stmt7_1_1_normal)
    (h325 : Stmt3_2_5) (hin : Input8_1_2) (h734 : Stmt7_3_4) : Stmt8_1_3_M24 :=
  stmt8_1_3_M24_of' a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved
    (stmtFSUModule_of_eight stmt3_2_2_eight_proved) h711 h325 (stmt8_1_1_final_q hC48 h711 h325) hin
    h734

theorem stmt8_3_1_of_steps
    (h832 : Stmt8_3_2) (h835 : Stmt8_3_5) (h8310 : Stmt8_3_10) (h8314 : Stmt8_3_14) :
    Stmt8_3_1 :=
  stmt8_3_1_of (stmtFSUModule_of_eight stmt3_2_2_eight_proved) input7_0_2_unique_proved
    input8_3_Q_proved input8_3_z h832 h835 h8310 h8314

end CFSG.Quasithin.H13
