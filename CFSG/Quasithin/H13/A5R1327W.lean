module

public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtE23FourFinal
public import CFSG.Quasithin.Background.SmithB45Holds
public import CFSG.Quasithin.H13.A5S1327zn
public import CFSG.Quasithin.H13.KGFactF618Big
public import CFSG.Quasithin.H13.NQCoreP134Input137Holds
public import CFSG.Quasithin.Vol2.Ch10SecI1CovH
public import CFSG.Quasithin.Vol2.Ch10SecQ1Facts
public import CFSG.Quasithin.Vol2.Ch3E213MG41SZ9
public import CFSG.Quasithin.Vol2.Ch3Sec3Frontier
public import CFSG.Quasithin.Vol2.Ch4Sec3L436InspM22
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D310D35
public import CFSG.Quasithin.Vol2.Ch5Sec1L34D35Holds
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem513Low
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Quot
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Two
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Final
public import CFSG.Quasithin.Vol2.GoldschmidtTD317
public import CFSG.Quasithin.Vol2.Ch4Sec3WFinal432R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem A5.rest1327_of_c48W
    (h_Stmt3_3_1 : CFSG.Quasithin.H13.Stmt3_3_1)
    (h_Stmt12_2_2 : CFSG.Quasithin.H13.Stmt12_2_2)
    (h_Stmt13_3_2 : CFSG.Quasithin.H13.Stmt13_3_2)
    (h_AS_C_1_34_corr : CFSG.Quasithin.MS93.burnsideC134w_AS_C_1_34_corrBig)
    (h_ASC48Statement_G : ∀ (G : Type) [Group G] [Finite G], CFSG.Quasithin.ASC48Statement G)
    (h_Gap437Sp4Z : CFSG.Quasithin.H13.Ch4.Gap437Sp4Z) :
    A5.Rest1327 := by
  have h_Theorem311Stmt := CFSG.Quasithin.H13.Frontier331.theorem311
  have h_Lemma13213 := CFSG.Quasithin.H13.A5.lemma13213_of (h331 := h_Stmt3_3_1)
      (h311 := h_Theorem311Stmt)
  have h_L2RankOneSylowFact := CFSG.Quasithin.H13.NQCat.l2RankOneSylowFact_holds
  have h_TheoremC58 := CFSG.Quasithin.theoremC58_proved
  have h_AS317Sylow := CFSG.Quasithin.as317Sylow_proved
  have h_AsB51 := CFSG.Quasithin.B5.asB51_holds
  have h_Stmt5_1_2 := CFSG.Quasithin.H13.stmt5_1_2_of_asB51 (h331 := h_Stmt3_3_1) (h51 := h_AsB51)
  have h_Insp436M22M23 := CFSG.Quasithin.H13.Ch4.I436.insp436M22M23_holds
  have h_Stmt4_3_2 := CFSG.Quasithin.H13.Ch4.stmt4_3_2_of_restW (hC48 := h_ASC48Statement_G)
      (hM2223 := h_Insp436M22M23)
      (h134 := h_AS_C_1_34_corr) (hZ := h_Gap437Sp4Z)
  have h_Stmt5_1_7_one_nat := CFSG.Quasithin.H13.stmt5_1_7_one_nat_of_rankOne
      (hR := h_L2RankOneSylowFact)
  have h_E22StatementNoN := CFSG.Quasithin.e22StatementNoN_proved
  have h_E23Statement := CFSG.Quasithin.C124.e23Statement_of_e22 (h22 := h_E22StatementNoN)
  have h_E23FourStatement := CFSG.Quasithin.E2.e23FourStatement_of (he22 := h_E22StatementNoN)
      (he23 := h_E23Statement)
  have h_StmtC113c := CFSG.Quasithin.H13.VolI.stmtC113c
  have h_Stmt5_1_7_one_A5 := CFSG.Quasithin.H13.stmt5_1_7_one_A5_of (he234 := h_E23FourStatement)
      (h432 := h_Stmt4_3_2) (hC113 := h_StmtC113c) (hR := h_L2RankOneSylowFact)
  have h_Stmt5_1_7_one := CFSG.Quasithin.H13.stmt5_1_7_one_of (h512 := h_Stmt5_1_2)
      (h432 := h_Stmt4_3_2) (hnat := h_Stmt5_1_7_one_nat) (hA5 := h_Stmt5_1_7_one_A5)
  have h_Stmt5_1_6_odd := CFSG.Quasithin.H13.stmt5_1_6_odd
  have h_Theorem316Statement := CFSG.Quasithin.Ch3T316W.theorem316Statement_holds
  have h_D35 := CFSG.Quasithin.H13.d35_proved
  have h_D310L2Fact := CFSG.Quasithin.H13.d310L2Fact_of_d35 (h35 := h_D35)
  have h_Facts10_1 := CFSG.Quasithin.Vol2.Ch10.SecA.facts10_1_holds
  have h_AsB45 := CFSG.Quasithin.asB45_holds
  have h_AS_I_1_6 := CFSG.Quasithin.ASInputs.lemI1_6_holds
  have h_L2FFModuleFact := CFSG.Quasithin.H13.l2FFModuleFact_of (h51 := h_AsB51)
  have h_AsB42 := CFSG.Quasithin.asB42_holds
  have h_Stmt5_1_3_low := CFSG.Quasithin.H13.stmt5_1_3_low_of (hF := h_L2FFModuleFact)
      (h42 := h_AsB42)
  have h_Stmt5_1_3_qhat := CFSG.Quasithin.H13.stmt5_1_3_qhat_of (hD := h_D310L2Fact)
      (hF := h_Facts10_1) (h45 := h_AsB45) (h16 := h_AS_I_1_6) (hlow := h_Stmt5_1_3_low)
  have h_Stmt5_1_3 := CFSG.Quasithin.H13.stmt5_1_3_of (h331 := h_Stmt3_3_1) (hC58 := h_TheoremC58)
      (h316 := h_Theorem316Statement) (h317 := h_AS317Sylow) (h512 := h_Stmt5_1_2)
      (hq := h_Stmt5_1_3_qhat)
  have h_Fact516Quot := CFSG.Quasithin.H13.fact516Quot
  have h_Fact516Two := CFSG.Quasithin.H13.fact516Two
  have h_Fact516Orth := CFSG.Quasithin.H13.fact516Orth
  have h_Stmt5_1_6_cases := CFSG.Quasithin.H13.stmt5_1_6_cases_of (h331 := h_Stmt3_3_1)
      (hC58 := h_TheoremC58) (h316 := h_Theorem316Statement) (h317 := h_AS317Sylow)
      (hR1 := h_L2RankOneSylowFact) (h512 := h_Stmt5_1_2) (h513 := h_Stmt5_1_3)
      (hQuot := h_Fact516Quot) (hTwo := h_Fact516Two) (hOrth := h_Fact516Orth)
  have h_Stmt5_1_6 := CFSG.Quasithin.H13.stmt5_1_6_of (h331 := h_Stmt3_3_1) (hC58 := h_TheoremC58)
      (hodd := h_Stmt5_1_6_odd) (hcases := h_Stmt5_1_6_cases)
  have h_Stmt5_1_7_two := CFSG.Quasithin.H13.stmt5_1_7_two_of (h331 := h_Stmt3_3_1)
      (hR := h_L2RankOneSylowFact) (hC58 := h_TheoremC58) (h317 := h_AS317Sylow)
      (h5171 := h_Stmt5_1_7_one) (h516 := h_Stmt5_1_6)
  have h_Input137 := CFSG.Quasithin.H13.NQCore.input137_holds
  have h_TheoremC126 := CFSG.Quasithin.theoremC126_proved
  have h_Theorem1391Statement := CFSG.Quasithin.A10.theorem1391
  have h_CaseS2A_1327 := CFSG.Quasithin.H13.A5.caseS2A_1327_of_c126 (h126 := h_TheoremC126)
      (h331 := h_Stmt3_3_1) (h1222 := h_Stmt12_2_2) (h517 := h_Stmt5_1_7_one)
      (h5172 := h_Stmt5_1_7_two) (h1332 := h_Stmt13_3_2) (h137 := h_Input137)
      (h1391 := h_Theorem1391Statement)
  have h_CaseS2_1327 := CFSG.Quasithin.H13.A5.caseS2_1327_of (h331 := h_Stmt3_3_1)
      (h1222 := h_Stmt12_2_2) (h5172 := h_Stmt5_1_7_two) (h1332 := h_Stmt13_3_2)
      (h512 := h_Stmt5_1_2) (h137 := h_Input137) (hA := h_CaseS2A_1327)
  have h_O2H0One1327 := CFSG.Quasithin.H13.A5.o2H0One1327_of (h331 := h_Stmt3_3_1)
      (h5172 := h_Stmt5_1_7_two)
  have h_GoldschmidtS3ListCat := CFSG.Quasithin.F6.goldschmidtS3ListCat_holds.{0}
  have h_F618ResidualRemaining := CFSG.Quasithin.F6.f618ResidualRemaining_of_goldschmidt
      (h := h_GoldschmidtS3ListCat)
  have h_F618ResidualRest := CFSG.Quasithin.F6.f618ResidualRest_of_remaining
      (h := h_F618ResidualRemaining)
  have h_TheoremF618Cat := CFSG.Quasithin.F6.theoremF618Cat_of_residualRest
      (h := h_F618ResidualRest)
  have h_FactF618Big := CFSG.Quasithin.H13.A5.factF618Big_holds
  have h_FactL2Three := CFSG.Quasithin.H13.A5.factL2Three_holds
  have h_Final1327CaseThree := CFSG.Quasithin.H13.A5.final1327CaseThree_of (h331 := h_Stmt3_3_1)
      (h1222 := h_Stmt12_2_2) (h5172 := h_Stmt5_1_7_two) (h311 := h_Theorem311Stmt)
      (h432 := h_Stmt4_3_2) (hL2 := h_FactL2Three)
  have h_Final1327 := CFSG.Quasithin.H13.A5.final1327_of (h331 := h_Stmt3_3_1)
      (h1222 := h_Stmt12_2_2) (h5172 := h_Stmt5_1_7_two) (h311 := h_Theorem311Stmt)
      (hF618 := h_TheoremF618Cat) (hBig := h_FactF618Big) (hThree := h_Final1327CaseThree)
  have h_Rest1327 := CFSG.Quasithin.H13.A5.rest1327_of (h13 := h_Lemma13213) (hS2 := h_CaseS2_1327)
      (hO2 := h_O2H0One1327) (hfin := h_Final1327)
  exact h_Rest1327

end CFSG.Quasithin.H13
