module

public import CFSG.Quasithin.H13.NQCatLemma128One
public import CFSG.Quasithin.Vol2.Ch10SecCWG
public import CFSG.Quasithin.Vol2.Ch10SecV1L
public import CFSG.Quasithin.Vol2.Ch10SecV1SK
public import CFSG.Quasithin.Vol2.Ch11L2Q5cJ4Orth
public import CFSG.Quasithin.Vol2.Ch11SecA312B1
public import CFSG.Quasithin.Vol2.Ch11SecAKA10
public import CFSG.Quasithin.Vol2.Ch11SecAKA9
public import CFSG.Quasithin.Vol2.Ch11SecAKB3
public import CFSG.Quasithin.Vol2.Ch11SecAKB5
public import CFSG.Quasithin.Vol2.Ch11SecAKC5
public import CFSG.Quasithin.Vol2.Ch11SecAKDj
public import CFSG.Quasithin.Vol2.Ch11SecAKE1
public import CFSG.Quasithin.Vol2.Ch11SecAKE3
public import CFSG.Quasithin.Vol2.Ch11SecAKM8
public import CFSG.Quasithin.Vol2.Ch11SecAKN7
public import CFSG.Quasithin.Vol2.Ch11SecBK10W
public import CFSG.Quasithin.Vol2.Ch11SecBK11G
public import CFSG.Quasithin.Vol2.Ch11SecBK3B
public import CFSG.Quasithin.Vol2.Ch11SecBK3C
public import CFSG.Quasithin.Vol2.Ch11SecBK6H
public import CFSG.Quasithin.Vol2.Ch11SecEK1A
public import CFSG.Quasithin.Vol2.Ch11SecEK1C
public import CFSG.Quasithin.Vol2.Ch11SecEK1G
public import CFSG.Quasithin.Vol2.Ch11SecEK1H
public import CFSG.Quasithin.Vol2.Ch11SecEK1I
public import CFSG.Quasithin.Vol2.Ch11SecEK2A
public import CFSG.Quasithin.Vol2.Ch11SecEK2B
public import CFSG.Quasithin.Vol2.Ch11SecGTMain
public import CFSG.Quasithin.Vol2.Ch11SecO11K
public import CFSG.Quasithin.Vol2.Ch11SecO1F
public import CFSG.Quasithin.Vol2.Ch11SecO6D
public import CFSG.Quasithin.Vol2.Ch11SecO6F
public import CFSG.Quasithin.Vol2.Ch11SecO6S6
public import CFSG.Quasithin.Vol2.Ch11SecO6S9
public import CFSG.Quasithin.Vol2.Ch11SecO6T
public import CFSG.Quasithin.Vol2.Ch11SecO7e
public import CFSG.Quasithin.Vol2.Ch11SecO7i
public import CFSG.Quasithin.Vol2.Ch11SecO7zb
public import CFSG.Quasithin.Vol2.Ch11SecOE3K
public import CFSG.Quasithin.Vol2.Ch11SecOE5H
public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4H
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGM
public import CFSG.Quasithin.Vol2.Ch11SecSWeylG
public import CFSG.Quasithin.Vol2.Ch11SecWire11F
public import CFSG.Quasithin.Vol2.Ch11SecWire11Q
public import CFSG.Quasithin.Vol2.Ch11SecWire11T
public import CFSG.Quasithin.Vol2.Ch11SKFSchreier
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch3T313C
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Emb
public import CFSG.Quasithin.Vol2.GoldschmidtA128
public import CFSG.Quasithin.Vol2.Ch11SecAKDb
public import CFSG.Quasithin.Vol2.Ch11SecEK1B
public import CFSG.Quasithin.Vol2.Ch11SecO5A
public import CFSG.Quasithin.Vol2.Ch11SecO7n
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BHat

public section

namespace CFSG.Quasithin.Vol2.Ch11.Wire11

theorem tmpL6_3_2_14_of_stmt3_2_14 (h : H13.Stmt3_2_14) : TmpL6_3_2_14 := by
  intro G _ _ T L hs hnab hK hT hL hq
  rw [solvRad_eq_map_solvableRadical]
  exact h G T L hs hnab hK hT hL hq


theorem proved
    : Proved where
  rankTwoQuasisimple := rankTwoQuasisimple_holds
  a3_7 := a37ForSQTK_proved
  a3_7Cat := a37ForSQTKCat_of_sqtk a37ForSQTK_proved
  a3_8 := a38ForSQTK_proved
  a3_8Cat := a38ForSQTKCat_of_sqtk a38ForSQTK_proved
  a3_9 := a39ForSQTK_proved
  a3_9Cat := a39ForSQTKCat_of_sqtk a39ForSQTK_proved
  stmt3_2_3 := H13.stmt3_2_3_of (a37ForSQTKCat_of_sqtk a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk
      a38ForSQTK_proved) (a39ForSQTKCat_of_sqtk a39ForSQTK_proved)
  a3_6 := H13.VolI.a36ForSQTK_holds
  stmtFSUChoice := Ch10.stmtFSUChoice_of_a36 (H13.stmt3_2_3_of (a37ForSQTKCat_of_sqtk
      a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk a38ForSQTK_proved) (a39ForSQTKCat_of_sqtk
      a39ForSQTK_proved)) H13.VolI.a36ForSQTK_holds
  d310C0 := H13.d310C0_holds
  tmpL6_3_2_2_two := Ch10.tmpL6_3_2_2_two_of H13.stmt3_2_2_eight_proved (H13.stmt3_2_3_of
      (a37ForSQTKCat_of_sqtk a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk a38ForSQTK_proved)
      (a39ForSQTKCat_of_sqtk a39ForSQTK_proved))
  tmpL6_3_2_2_four := tmpL6_3_2_2_four_of (Ch10.tmpL6_3_2_2_two_of H13.stmt3_2_2_eight_proved
      (H13.stmt3_2_3_of (a37ForSQTKCat_of_sqtk a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk
      a38ForSQTK_proved) (a39ForSQTKCat_of_sqtk a39ForSQTK_proved)))
  e22StatementNoN := E2.E22N.e22StatementNoN_of_asc80 (E2P.Asc80.asc80L3Eps_of
      (E2P.Asc80.asc80L3Stmt_of A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of (A312U3.su3OddIrr_of
      (A312U3.su3OddIrrGe7_of A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds
      A312U3.su3NoPSL2_holds) A312U3.su3OddIrrSmall_holds)))
  theoremC58 := Ch3T316W.theoremC58_of_atoms (E2.E22N.e22StatementNoN_of_asc80
      (E2P.Asc80.asc80L3Eps_of (E2P.Asc80.asc80L3Stmt_of A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of
      (A312U3.su3OddIrr_of (A312U3.su3OddIrrGe7_of A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds
      A312U3.su3NoPSL2_holds) A312U3.su3OddIrrSmall_holds))))
  asB42 := asB42_of_families asB42U3Even_holds asB42Sz_holds asB42TrialityD4_holds
      (asB42ReeF4_of_large asB42ReeF4Large_holds) asB42L2Even_holds asB42L32_holds asB42L3Even_holds
      asB42Sp4Even_holds (asB42G2Even_holds gm04G2EvenFFNatural_holds)
      (asB42U33_of_six B42U33.u33SixNatural) asB42L42_holds asB42L52_holds asB42Alt5_holds
      asB42Alt6_holds asB42HatA6_holds asB42Alt7_holds
  as317Sylow := as317Sylow_of_nonsolvable (Ch3n317Ker.as317SylowNonsolvable_of_e23
      (GE23.e23Nonsolvable_of_inputs B15P4.asB15Part4 (B69.asB69Component_of_deep_inputs_fourNoN
      (asB42_of_families asB42U3Even_holds asB42Sz_holds asB42TrialityD4_holds (asB42ReeF4_of_large asB42ReeF4Large_holds)
      asB42L2Even_holds asB42L32_holds asB42L3Even_holds asB42Sp4Even_holds (asB42G2Even_holds
      gm04G2EvenFFNatural_holds) (asB42U33_of_six B42U33.u33SixNatural) asB42L42_holds
      asB42L52_holds asB42Alt5_holds asB42Alt6_holds asB42HatA6_holds asB42Alt7_holds)
      asA21SQTKSection (E2.E22N.e22StatementNoN_of_asc80 (E2P.Asc80.asc80L3Eps_of
      (E2P.Asc80.asc80L3Stmt_of A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of (A312U3.su3OddIrr_of
      (A312U3.su3OddIrrGe7_of A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds
      A312U3.su3NoPSL2_holds) A312U3.su3OddIrrSmall_holds)))) (B69.asB69DeepInputsFour_holds
      (E2.E22N.e22StatementNoN_of_asc80 (E2P.Asc80.asc80L3Eps_of (E2P.Asc80.asc80L3Stmt_of
      A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of (A312U3.su3OddIrr_of (A312U3.su3OddIrrGe7_of
      A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds A312U3.su3NoPSL2_holds)
      A312U3.su3OddIrrSmall_holds)))))) (B69.b69One_of_E22NoN (
          asB42_of_families asB42U3Even_holds asB42Sz_holds
      asB42TrialityD4_holds (asB42ReeF4_of_large asB42ReeF4Large_holds) asB42L2Even_holds
      asB42L32_holds asB42L3Even_holds asB42Sp4Even_holds (asB42G2Even_holds
      gm04G2EvenFFNatural_holds) (asB42U33_of_six B42U33.u33SixNatural) asB42L42_holds
      asB42L52_holds asB42Alt5_holds asB42Alt6_holds asB42HatA6_holds asB42Alt7_holds)
      B15P4.asB15Part4 asA21SQTKSection (E2.E22N.e22StatementNoN_of_asc80 (E2P.Asc80.asc80L3Eps_of
      (E2P.Asc80.asc80L3Stmt_of A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of (A312U3.su3OddIrr_of
      (A312U3.su3OddIrrGe7_of A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds
      A312U3.su3NoPSL2_holds) A312U3.su3OddIrrSmall_holds)))) B69.noStrongSL3
      (B69.noStrongSp4_of_one B69.noStrongSp4One)) (E2.E22N.e22StatementNoN_of_asc80
      (E2P.Asc80.asc80L3Eps_of (E2P.Asc80.asc80L3Stmt_of A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of
      (A312U3.su3OddIrr_of (A312U3.su3OddIrrGe7_of A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds
      A312U3.su3NoPSL2_holds) A312U3.su3OddIrrSmall_holds))))))
  asB56 := asB56_holds
  asB51 := B5.asB51_holds
  factG2AdjointOrder := SecA.factG2AdjointOrder_holds
  facts02 := ⟨SecA.factG2AdjointOrder_holds, KGNat.factG2DerivedOrder_holds,
      SecA.factG2DerivedTwoOrder_holds, SecS.factL34_holds, KGNat.factNoGraphSL3_holds,
      KGNat.factNoGraphSp4_holds⟩
  as_I_1_6 := ASInputs.lemI1_6_holds
  factTwist := SecA.factTwist_holds
  factNot4213 := SecB.factNot4213_holds
  theorem311Stmt := theorem311Stmt_of_C58 (Ch3T316W.theoremC58_of_atoms
      (E2.E22N.e22StatementNoN_of_asc80 (E2P.Asc80.asc80L3Eps_of (E2P.Asc80.asc80L3Stmt_of
      A38c15.sl3OddIrr) (E2P.Asc80.asc80U3Stmt_of (A312U3.su3OddIrr_of (A312U3.su3OddIrrGe7_of
      A312U3.su3NoPSL3_holds A312U3.su3PSU3Case_holds A312U3.su3NoPSL2_holds)
      A312U3.su3OddIrrSmall_holds)))))
  as_E_6_12 := E6.as_E_6_12_of (E6.e611ComponentCase_of (E6.e68ComponentFacts_of_cases
      (H13.KG68.e68ComponentFactsLie_of_inner (QuasithinUnique.Ch1.evenLieAutInner_of_tits
      QuasithinUnique.K1.titsSylowCentralizingAutInner) H13.KG68.u33AutInner_holds)
      (H13.KG68.e68ComponentFactsCover_of_inner (QuasithinUnique.Ch1.evenLieAutInner_of_tits
      QuasithinUnique.K1.titsSylowCentralizingAutInner)) H13.KG68.e68ComponentFactsAlt_holds
      H13.KG68.e68ComponentFactsL2p_holds (H13.KG68.e68ComponentFactsSpor_of
      Ch10.A312A.sporadicAutInner_proved (H13.KG68.sporadicSylowCenterCyclic_of_j4
      H13.KG68.j4SylowCenterCyclic_holds))) lemma115_3_List_native)
  lemE6_6_four := E6.as_E_6_6_four_proved
  as_E_6_14 := Wire11.as_E_6_14_holds
  a318Facts := a318Facts_of_two (qSporOutTwo_of_orderThreeCentralizerBound
      j4OrderThreeCentralizerBound_holds) R3c18.qLiePRank_holds
  a319Facts := Ch10.a319Facts_holds
  facts12 := SecA.facts12_of SecA.factCartanPointG2_holds SecA.factList2Table_holds
      SecA.factG2AdjointOrder_holds SecA.fact3D4Order_holds
  factList3Table := SecA.factList3Table_holds
  facts12b := SecA.facts12b_of SecA.factList3Table_holds SecA.factOuterLevi_holds
      SecA.factFieldAutPointG2_holds SecA.factJ1_holds
  facts12c := SecA.facts12c_of (SecA.factModules3n_of_open SecA.factModulesSL3_holds
      CFSG.Quasithin.H13.HatA7.hatA7Faithful6_holds) SecA.factA7SectionCent_holds SecA.factCartanLineG2_holds
  factL2Parabolic := SecA.factL2Parabolic_holds
  facts11 := ⟨KGNat.factPointSL3_holds, KGNat.factPointSp4_holds, G2Q8.factPointG2A_holds,
      SecA.factL2Parabolic_holds⟩
  factParabGen := SecS.factParabGen_holds
  a3_6CoreCat := QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved
  tmp1_3_3 := tmp1_3_3_holds
  a312ForSQTKCat := QuasithinUnique.Vol2Native.a312ForSQTKCat_of_facts
      (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved (a37ForSQTKCat_of_sqtk
      a37ForSQTK_proved) (a39ForSQTKCat_of_sqtk a39ForSQTK_proved)
  a312ForSQTK := a312ForSQTK_of_cat (QuasithinUnique.Vol2Native.a312ForSQTKCat_of_facts
      (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved (a37ForSQTKCat_of_sqtk
      a37ForSQTK_proved) (a39ForSQTKCat_of_sqtk a39ForSQTK_proved))
  factShapeInspect := SecS.factShapeInspect_of SecS.factU35UniqueL24_holds
  factBorelShape := SecS.factBorelShape_holds
  factParabTwo := SecS.factParabTwo_holds
  lemma128Four := Ch1Four.lemma128Four_of (a312ForSQTK_of_cat
      (QuasithinUnique.Vol2Native.a312ForSQTKCat_of_facts
      (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved (a37ForSQTKCat_of_sqtk
      a37ForSQTK_proved) (a39ForSQTKCat_of_sqtk a39ForSQTK_proved)))
  lem1_2_8_one := H13.NQCat.lemma128One_holds
  factJ4UniqueL24 := SecS.factJ4UniqueL24_holds
  as_A_1_28 := ASInputs.as_A_1_28_holds
  factShapeWeyl := SecS.SWeyl.factShapeWeyl_holds
  factSchreierComp := SecS.factSchreierComp_of CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  l2pSignalizerFact := SecD.l2pSignalizerFact_holds
  sl2pSignalizerFact := SecE.sl2pSignalizerFact_holds
  facts41 := ⟨KGNat.vecTransFacts_holds, (⟨KGNat.factFlagSL3_holds, KGNat.factFlagSp4_holds,
      G2Q8.factFlagG2_holds, KGNat.factLeviSL3_holds, KGNat.factLeviSp4_holds,
      G2Q8.factLeviG2_holds, KGNat.factN13Sp4_holds, G2Q8.factN13G2_holds⟩), SecB.factR2Gen_holds,
      SecE.factSp4R2Big_holds, SecE.factG2LongRoot_holds, SecA.factG2AdjointOrder_holds,
      KGNat.factG2DerivedOrder_holds, (⟨KGNat.factParInSL3_holds, SecE.factParInSp4_holds,
      SecE.factParInG2_holds⟩), SecD.l2pSignalizerFact_holds, SecE.sl2pSignalizerFact_holds,
      SecE.factCase1Comm_holds⟩
  as_A_1_12 := Ch10.as_A_1_12_holds
  facts15 := ⟨SecA.factRankTwoLieSp4G2_holds, KGNat.factSylowLeviSL3_holds,
      KGNat.factSylowLeviSp4_holds, G2Q8.factSylowLeviG2_holds, KGNat.factPointCentralizerSL3_holds,
      KGNat.factRadicalFixedSL3_holds, KGNat.factRadicalFixedSp4_holds,
      SecA.factRadicalFixedG2_holds, KGNat.factRadicalPointSL3_holds,
      KGNat.factRadicalPointSp4_holds, SecA.factRadicalPointG2_holds⟩
  e114LieCited := SecE3.Lie3.e114LieCited_holds
  factNotSmall443 := SecB.factNotSmall443_holds
  a312Facts := a312Facts_of_cat (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact
  l2Overgroup := SecB.l2Overgroup_of (a312Facts_of_cat
      (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact) H13.VolI.a36ForSQTK_holds a37ForSQTK_proved a39ForSQTK_proved
      H13.NQCat.lemma128One_holds (Ch10.stmtFSUChoice_of_a36 (H13.stmt3_2_3_of
      (a37ForSQTKCat_of_sqtk a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk a38ForSQTK_proved)
      (a39ForSQTKCat_of_sqtk a39ForSQTK_proved)) H13.VolI.a36ForSQTK_holds)
  factMathieuOrders := H13.factMathieuOrders_holds
  l2NotJ4Orth := SecB.l2NotJ4Orth_of (a312Facts_of_cat
      (QuasithinUnique.Vol2Native.A312L.a312ListFactsCat_of_families
      QuasithinUnique.Vol2Native.threeCoverFactCat
      (QuasithinUnique.Vol2Native.A312L.a312Families_of_residual (A38c14.A312ResidualRest.toResidual
      (A38c15.A312ResidualRest10.toRest (A38c17.A312ResidualRest7.toRest10 A312J2.famJ2_holds
      (A38c17.A312ResidualRest6.toRest7 (A38c17.A312ResidualRest4.toRest6
      (A38c17.A312ResidualRest3.toRest4 (A38c17.A312ResidualRest2.toRest3
      (A38c17.a312ResidualRest2_of_j4 J4Ov.j4OvergroupLocal_holds J4Fam.j4M2Residual))))))))))
      a312SL2Fact) H13.VolI.a36ForSQTK_holds a37ForSQTK_proved a39ForSQTK_proved
      H13.factMathieuOrders_holds
  factG2Simple := SecB.factG2Simple_holds
  stmt4_4_13Lie := H13.stmt4_4_13Lie_holds
  as_G_1_6 := Ch10.asG16_holds
  lemI1_3_L2 := SecH.as_I_1_3_L2_holds
  facts42 := ⟨SecE.a312A5Fact_holds, SecE.a312L2pFact_holds, SecE.cartanPointFact_holds,
      SecE.list11_1_1TwoQuasisimpleFact_holds⟩
  facts43 := ⟨SecE.factOut2SL2_holds, SecE.factOut2L2p_holds, SecE.factOut2Case1_holds,
      SecE.factFixPointSL3_holds, SecE.factFixPointSp4_holds, SecE.factFixPointG2_holds⟩
  facts42S1 := ⟨SecE.a312List11Fact_holds, SecE.factM23J4_holds⟩
  facts42S3 := ⟨SecE.list11_1_1List701Fact_holds, SecE.list11_1_1ThreeQuasisimpleFact_holds⟩
  facts44 := ⟨SecE.factTorusPointSL3_holds, SecE.factTorusPointSp4_holds,
      SecE.factTorusPointG2_holds, SecE.factCentLeviSL3_holds, SecE.factCentLeviSp4_holds,
      SecE.factCentLeviG2_holds, SecE.factBorelNotTwo_holds⟩
  factCase1NormL1 := SecD.O6S.factCase1NormL1_holds
  factCase1GL8 := SecD.O6S.factCase1GL8_holds
  factCCompTorus := SecD.BK10.factCCompTorus_holds
  prop121Three := QuasithinUnique.Vol2Native.prop121Three_of_a3 (a37ForSQTKCat_of_sqtk
      a37ForSQTK_proved) (a38ForSQTKCat_of_sqtk a38ForSQTK_proved)
  factM2Case1 := SecD.O6S.factM2Case1_holds
  factM2Case1Prime := SecD.O6S.factM2Case1Prime_holds
  as_I_1_3_Sp4 := ASInputs.as_I_1_3_Sp4_holds
  factCase1Shape := SecG.factCase1Shape_holds
  factTransv11_5_8 := SecG.factTransv11_5_8_of SecG.factL2pInvol_holds SecG.factL2pListMod5_holds
      SecG.factCase1Shape_holds
  factCase1PrimeAct := SecD.O6S.factCase1PrimeAct_holds
  lem3_2_2_eight := H13.stmt3_2_2_eight_proved
  lem3_2_8 := H13.stmt3_2_8_of asB42_holds H13.VolI.asI16Cover328_holds
  lem3_2_14 := fun hl h37 h38 hfsu h701 h316 => tmpL6_3_2_14_of_stmt3_2_14
      (H13.NQBlock.stmt3_2_14_of (OE3.noOddLinear_of h37 h38 hfsu h701) (H13.lemma3_2_13Consumed_of
      h316 H13.U3.uniqueThreeCaseModelReduction_holds) (OE4.lemma3_2_14HomocyclicConsumed_of h316
      H13.U3.uniqueThreeCaseModelReduction_holds) hl)

end CFSG.Quasithin.Vol2.Ch11.Wire11
