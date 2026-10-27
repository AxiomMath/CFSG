module

public import CFSG.Quasithin.H13.A5S1328VertexA5
public import CFSG.Quasithin.H13.A5NoC134

public section

namespace CFSG.Quasithin.H13.A5

section SliceS1517
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint
open scoped MatrixGroups

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

section Ident

variable {H I : Subgroup G} (hH : H ∈ S.Hz) (D : Data13515 S H I)
include hH D

theorem amalgam_U42_corrected_slices (hA5 : CFSG.Quasithin.F112R.F112SliceA5) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups H (L ⊔ T)) := by
  have hnorm : (T.subgroupOf (T ⊔ borelOf I T)).Normal := by
    rw [sup_eq_left.2 (S.borel_I_le_T hH D), Subgroup.subgroupOf_self]
    infer_instance
  obtain ⟨L1', L2', hswap, hZ, hlist, -⟩ :=
    hA5 G I L T ⟨S.hyp111 hH D, S.isQuasithinSub _, Or.inl hnorm⟩
      (Or.inr (Or.inl ⟨D.I_S3, S.isL2Quot_two_L⟩))
  have hZI : centerOf T ≤ Subgroup.centralizer (I : Set G) := by
    intro x hx
    have hxV1 := S.center_T_le_V1 hH D hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG1 : y ∈ S.G1 := D.H_eq ▸ D.I_le hy
    rw [← S.centralizer_V1] at hyG1
    exact (Subgroup.mem_centralizer_iff.mp hyG1 x hxV1).symm
  obtain ⟨h1', h2'⟩ : L1' = I ∧ L2' = L := by
    rcases hswap with h | ⟨h1, -⟩
    · exact h
    · exfalso
      rw [h1] at hZ
      exact S.not_center_T_le_centralizer_L (hZ (Or.inl hZI))
  rw [h1', h2'] at hlist
  have hcI := S.card_oTwoQuot_I D
  have hcL := S.card_oTwoQuot_L
  have hcI' : Nat.card (OTwoQuot I) = 6 := hcI
  have hamal : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T)
      (L ⊔ bigB I L T)) (IsLieOverTwo .PSU 4 1) ∨
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups (I ⊔ bigB I L T) (L ⊔ bigB I L T)) := by
    unfold F112ListC at hlist
    rcases hlist with ⟨f, hf, -, h⟩ | ⟨f, hf, -, h⟩ | ⟨f, hf, -, hI, hL, -⟩ |
        ⟨f, hf, -, hI, -⟩ | ⟨a, -, -, -, hL, -⟩ | ⟨f, hf, ham, hI, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, hL, -⟩ | ⟨-, -, -, hL, -⟩ | ⟨-, hI, -⟩ | ⟨-, -, -, ⟨eL⟩, -⟩ | ⟨-, -, -, hL, -⟩ |
        ⟨-, -, -, hL, -⟩
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h1
        have h2 : Nat.card I ≤ Nat.card ↥(I ⊔ T) :=
          Subgroup.card_le_of_le le_sup_left
        rw [S.card_I D, h1] at h2
        exact absurd h2 (by decide)
    · exfalso
      rcases h with ⟨hf2, -, hlin, -⟩ | ⟨-, ⟨e⟩, -⟩
      · have := isLin2Type_eq_one_of_card_six hf hlin hcI'
        omega
      · have h1 := Nat.card_congr e.toEquiv
        rw [Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin,
          Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1
        have h2 : Nat.card I ≤ Nat.card ↥(I ⊔ T) :=
          Subgroup.card_le_of_le le_sup_left
        rw [S.card_I D, h1] at h2
        exact absurd h2 (by decide)
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by omega) hcI
      omega
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by omega) hL hcL
      omega
    · have h1 := hI.eq_one_of_card_eq_six hf hcI
      subst h1
      exact ham
    · exfalso
      have h1 := eq_two_of_isL2Quot_card_sixty (by norm_num) hL hcL
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have h1 := hI.eq_one_of_card_eq_six (by norm_num) hcI
      omega
    · exfalso
      have h1 := Nat.card_congr eL.toEquiv
      rw [hcL, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact absurd h1 (by decide)
    · exfalso
      have := hL.card le_rfl
      omega
    · exfalso
      have := hL.card le_rfl
      omega
  obtain ⟨h1, h2⟩ := S.sup_bigB hH D
  rwa [h1, h2] at hamal

theorem prop_13_5_17_corrected_slices (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hamal := S.amalgam_U42_corrected_slices hH D hA5
  have hHM : ¬ H ⊔ (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) := fun h =>
    hH.2.2 (le_sup_left.trans h)
  have ho2 : pCoreOf 2 (H ⊔ (L ⊔ T)) = ⊥ := S.o2_eq_bot_of_not_le le_sup_right hHM
  have hzH : S.z ∈ H := by
    rw [D.H_eq]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzc : S.z ∈ centerOf (H ⊓ (L ⊔ T)) := by
    refine ⟨⟨hzH, le_sup_right (a := L) (S.V_le_T S.z_mem_V)⟩, ?_⟩
    show S.z ∈ Subgroup.centralizer ((H ⊓ (L ⊔ T) : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG1 : x ∈ S.G1 := D.H_eq ▸ hx.1
    exact Subgroup.mem_centralizer_singleton_iff.mp hxG1
  have hCz : Subgroup.centralizer ({S.z} : Set G) ≤ H := by rw [D.H_eq]; rfl
  have hN1 : Subgroup.normalizer (centerOf (pCoreOf 2 H) : Set G) = H := by
    rw [D.center_QH, ← S.G1_eq_normalizer, D.H_eq]
  have hN2 : Subgroup.normalizer (centerOf (pCoreOf 2 (L ⊔ T)) : Set G) = L ⊔ T := by
    rw [D.V_eq]
    have hcV : centerOf V = V := le_antisymm inf_le_left (le_inf le_rfl
      (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
        congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)))
    rw [hcV]
    exact le_antisymm (S.NV_le_M.trans D.M_eq.le) S.reduced.2.1
  exact hF431 G S.h13.simple S.h13.nonabelian H (L ⊔ T) S.z hamal ho2 S.z_sq S.z_ne_one hzc hCz
    hN1 hN2

end Ident

end Setting

end SliceS1517

section SliceTop
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem thm_13_6_1_corrected_slices (h1323 : Input1323Two) (h1336 : Input1336)
    (h13515 : Input13515) (h13518 : Input13518) (h136 : Input136)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (hF431 : StmtF431U42) :
    LieModel G .PSU 4 2 1 ∨ LieModel G .PSL 4 3 1 := by
  have hG1 := S.G1_mem_Hz h1336
  by_cases hab : IsElemAbelian 2 (conjClosure S.V3 S.G1)
  ·
    exact absurd (((S.tfae_13_5_10 h1323 hG1).out 2 3).1 hab) (h136 G T L V S)
  ·
    obtain ⟨H, hH, hna, hn⟩ := h13518 G T L V S hab
    obtain ⟨I, D⟩ := h13515 G T L V S H hH hn hna
    exact S.prop_13_5_17_corrected_slices hH D hA5 hF431

end Setting

end SliceTop

section SliceGlobal
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

theorem stmt13_6_1_of_inputs_slices (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h1323 : Input1323Two) (h1336 : Input1336)
    (h13515 : Input13515) (h13518 : Input13518) (h136 : Input136)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (hF431 : StmtF431U42) : Stmt13_6_1 := by
  intro G _ _ T L h hLA5
  obtain ⟨V, ⟨S⟩⟩ := exists_setting h132two h132fsu h132A5 h hLA5
  exact S.thm_13_6_1_corrected_slices h1323 h1336 h13515 h13518 h136 hA5 hF431

end SliceGlobal

section SliceFinal
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint
open scoped commutatorElement

theorem stmt13_6_1_of_ext_slices
    (h132two : Stmt13_3_2_two) (h132fsu : Stmt13_3_2_three_fsu)
    (h132A5 : Stmt13_3_2_three_A5) (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) (hG248 : StmtG248)
    (h13518 : Input13518) (h136 : Input136) (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (hF431 : StmtF431U42) :
    Stmt13_6_1 := by
  have h1323 := input1323Two_of h311 h1222
  have h1326 := input1326Two_of h1222 h517
  have h1336 := input1336_of h331 h1327
  exact stmt13_6_1_of_inputs_slices h132two h132fsu h132A5 h1323 h1336
    (input13515_of h1323 h1326 h1336 VolI.stmtF956i hG248 VolI.stmtC113c) h13518 h136 hA5
    hF431

end SliceFinal

section SliceTop1332
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt13_6_1_of_1332_slices (h1332 : Stmt13_3_2)
    (h311 : Theorem311Stmt) (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h331 : Stmt3_3_1)
    (h1327 : Stmt13_2_7) (hG248 : StmtG248) (h13518 : Input13518) (h136 : Input136)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (hF431 : StmtF431U42) : Stmt13_6_1 := by
  refine stmt13_6_1_of_ext_slices (fun G _ _ T L hH K hK => (h1332 G T L hH K hK).2.1) ?_
    (stmt13_3_2_three_A5_of h1332) h311 h1222 h517 h331 h1327 hG248 h13518 h136 hA5 hF431
  intro G _ _ T L hH K hK
  refine ⟨(h1332 G T L hH K hK).2.2.1.1, fun V hV => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := (h1332 G T L hH K hK).2.2.1.2 V hV
  exact ⟨h1, h2, h3⟩

end SliceTop1332

section SliceVertex
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

theorem stmt13_2_7_of_caseS2A_c126_corrected_slices
    (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (h523 : Stmt5_2_3)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (hE22 : E2.E22StatementNoN)
    (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big) (hL2 : FactL2Three) (h1332 : Stmt13_3_2)
    (h512 : Stmt5_1_2) (h137 : EmptyFaithfulMultiple.Input137)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (h126 : TheoremC126) (hA : CaseS2A_1327) : Stmt13_2_7 :=
  stmt13_2_7_of_caseS2A_ofNoN h331 h311 h432 h523 h1222 h5172 hE22
    (res1328a_of_corrected_A5 (stmt13_3_2_two_of h1332) (stmt13_3_2_three_fsu_of h1332)
      (stmt13_3_2_three_A5_of h1332) h331 h512 h5172 hA5 h126)
    hF618 hBig hL2 h1332 h512 h137 hA

end SliceVertex

section SliceS1327zn
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem stmt13_2_7_of_c126_slices
    (h331 : Stmt3_3_1) (h311 : Theorem311Stmt) (h432 : Stmt4_3_2) (h523 : Stmt5_2_3)
    (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one) (h5172 : Stmt5_1_7_two)
    (hE22 : E2.E22StatementNoN) (hF618 : F6.TheoremF618Cat) (hBig : FactF618Big)
    (hL2 : FactL2Three) (h1332 : Stmt13_3_2) (h512 : Stmt5_1_2)
    (h137 : EmptyFaithfulMultiple.Input137) (h1391 : Theorem1391Statement)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5) (h126 : TheoremC126) : Stmt13_2_7 :=
  stmt13_2_7_of_caseS2A_c126_corrected_slices h331 h311 h432 h523 h1222 h5172 hE22 hF618 hBig hL2
    h1332 h512 h137 hA5 h126 (caseS2A_1327_of_c126 h126 h331 h1222 h517 h5172 h1332 h137 h1391)

end SliceS1327zn

section SliceNoC134
open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt13_6_1_of_open_noC134_slices
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two)
    (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h523 : Stmt5_2_3)
    (hA5 : CFSG.Quasithin.F112R.F112SliceA5)
    (h132 : ASInputs.AS_C_1_32) :
    Stmt13_6_1 := by
  have h517 : Stmt5_1_7_one := CFSG.Quasithin.H13.stmt5_1_7_one_of_asB51' h331 B5.asB51_holds h432
    (E2.e23FourStatement_of e22StatementNoN_proved
      (C124.e23Statement_of_e22 e22StatementNoN_proved))
  have h137 : EmptyFaithfulMultiple.Input137 := NQCore.input137_holds
  have h56 : AsB56 := asB56_holds
  have h311 : Theorem311Stmt := theorem311_of_solvable_nonsolvable
    (EmptyFaithfulMultiple.input311Solvable_of (G64.inputC512G64_of_lemmaG64
      (G64.lemmaG64_of_b5 h56))) C58NS.theorem311Nonsolvable_proved
  have hNoN : E2.E22StatementNoN := e22StatementNoN_proved
  have h126 : TheoremC126 := theoremC126_proved
  have hF618 : F6.TheoremF618Cat := F6.theoremF618Cat_of_residualRest
    (F6.f618ResidualRest_of_remaining (F6.f618ResidualRemaining_of_goldschmidt
      (F6.goldschmidtS3ListCat_of_charTwoLarge (F6.goldschmidtCharTwoLarge_of_pair
        F6.GoldAmLarge.goldschmidtCharTwoLargePair_holds))))
  have h512 : Stmt5_1_2 := H13.stmt5_1_2_of_asB51 h331 B5.asB51_holds
  have h1327 : Stmt13_2_7 := stmt13_2_7_of_c126_slices h331 h311 h432 h523 h1222 h517 h5172 hNoN hF618
    factF618Big_holds factL2Three_holds h1332 h512 h137 A10.theorem1391 hA5 h126
  have h1323 : Input1323Two := input1323Two_of h311 h1222
  have h1326 : Input1326Two := input1326Two_of h1222 h517
  have h1336 : Input1336 := input1336_of h331 h1327
  have h132two : Stmt13_3_2_two := H13.stmt13_3_2_two_of h1332
  have h132fsu : Stmt13_3_2_three_fsu := H13.stmt13_3_2_three_fsu_of h1332
  have h132A5 : Stmt13_3_2_three_A5 := stmt13_3_2_three_A5_of h1332
  have h36 : A36ForSQTK := VolI.a36ForSQTK_holds
  have h37 : Vol2Native.A37ForSQTKCat := Vol2Native.a37ForSQTKCat_proved
  have h38 : Vol2Native.A38ForSQTKCat := CFSG.Quasithin.H13.A5.a38ForSQTKCat_holds
  have h39 : Vol2Native.A39ForSQTKCat := Vol2Native.a39ForSQTKCat_proved
  have hF318 : A318Facts := a318Facts_of_two qSporOutTwo_holds R3c18.qLiePRank_holds
  have hKF : KnownFacts15122Types := knownFacts15122Types_final
  have hAB : Elim1366AB := elim1366AB_of h1222 h517 h331 h1327 h1336 hF318 h36 h37 h38 hKF
    KG68.evenLieAutInner_holds KG68.trialityTwoSylowCenterCyclic_holds
    KG68.titsSylowCenterCyclic_holds ZCentLie.factLieZCent_holds KGLieOut.factLieOutAbelian_holds
    ZCentLie.factLieZCentPGL3_holds KGL3Syl.factL3SylowCenterCyclic_holds
    Vol2Native.lemma122A_proved (elim1366Sp4_of h1222 h517 h37 h38)
    (elim1366SzPair_of h1222 h517 h37 h38)
  have h1623 : Lemma13623C := lemma13623C_of_b51_sq h1222 h517 h132two h132fsu h132A5 h331 h1327 h36
    h37 h38 h39 h132
    (lem13622Case4Z0_of_sq h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39
      MS93.MRes.c134Case4Lemma45CorrSq_holds)
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    (lemma13620L45_of h1222 h517 hF318 h36 h37 h38 hKF)
    (o3Prime1367_of h1222 h517 hF318 h36 h37 h38 hKF) B5.asB51_holds
  have hmain : Main1367 := main1367_of_inputs_noC134 h126 (C124.e23Statement_of_e22 hNoN) h1222
    h517 h56 h132two h132fsu h132A5 h331 h1327 h36 h37 h38 h39 h132
    (fun G _ _ => C124.c124StatementSQTK_of_e22 hNoN G) hF318 hKF
    (lem13622A7Block_of h1222 h517) h1623
  have hSp : FactConfSpor := factConfSpor_of (Ch1.sporadicAutInner_of_residual
    (Ch1.sporadicResidualAutInner_of_J4 (Ch1.j4AutInner_of_outOdd Setup.X1.j4OuterOdd)))
    KG68.sporadicSylowCenterCyclic_holds
  have h1366 : Lemma1366 := lemma1366_of h1222 h517 lemma115_3_List_native hAB
    (elim1366CD_holds h1222 h517)
    (elim1366EF_of_facts h1222 h517 factConfL33_holds factConfL2_holds hSp)
  have h1367 : Thm13_6_7 := thm13_6_7_of h1222 h517 h1366 hmain
  have h312 : A312ForSQTK := A38c14.a312ForSQTK_of_residual A3Facts.a134ForSQTK
    A3Facts.schreierSQTK A38c17.a312ResidualRest2_holds.toRest3.toRest4.toRest10.toRest
  have hD391 : D391 := d391L_of_deep (d391Deep_of_inputs H13.d35_proved B5.asB51_holds
    asA21SQTKSection)
  have hfin : Fin136 := fin136_of_hubs h1323 h1336 h523 h312
    (d310_of_unfaithful H13.d35_proved hD391 d310Unfaith_holds) hD391 asB45_holds
  exact stmt13_6_1_of_1332_slices h1332 h311 h1222 h517 h331 h1327 VolI.stmtG248
    (input13518_of_b45 h1323 h1326 h1336 asB45_holds)
    (input136_of_1332 h1367 h1326 h1336 h1323 h1332 hfin) hA5 F431.U42.stmtF431U42_holds

end SliceNoC134

end CFSG.Quasithin.H13.A5

end
