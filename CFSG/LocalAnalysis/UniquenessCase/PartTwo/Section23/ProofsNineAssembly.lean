module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNinePointStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23Omega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineAdjMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineSemireg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineC2Emb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA4Quot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s23_9_common_of (D : Data G) (Ch : Choice2011 G)
    (h209 : S20_9 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch)
    (h71 : S23_7_1 D Ch) (h8 : S23_8 D Ch) (hSigma : UC6S846.SigmaStd D)
    (h847 : R847ThinCZ D) (hTabA : KTab23a) (hTabD : KTab23d)
    (hOrd : KOrdNatural) (hSchur : KSchurL2) (hSub : KSub23) (hSubS : KSub23Simple)
    (hGen : KGen) (hC1Schur : KSchurC1) (hGenO6 : KGenO6p) (hSchurO6 : KSchurO6p)
    (hOut : KOut23) (hSU44 : KSU44) (hAdj : KAdj) (h462 : UCK.K462)
    (h76 : F07.R76Sig D) :
    S23_9_PointStab D Ch ∧ S23_9_B23 D Ch ∧ S23_9_NotSp4SU4O6m D Ch ∧
      S23_9_NotO6p D Ch := by
  have hPS : S23_9_PointStab D Ch := s23_9_PointStab_of D Ch (h4 := h4) (hO2 := s23_9_O2L_of)
  have hSem : S23_9_Semireg D Ch :=
    s23_9_Semireg_of D Ch (h71 := h71) (hsig := hSigma.nonempty)
  have hA0 : S23_9_A0 D Ch := s23_9_A0_of D Ch
  have hA1 : S23_9_A1 D Ch := s23_9_A1_of D Ch (h53 := h53)
  have hASem : S23_9_ASem D Ch := s23_9_ASem_of D Ch (h54 := h54) (h6 := h6) (hSem := hSem)
  have hAdjData : S23_9_Adj D Ch :=
    s23_9_Adj_of D Ch (h2 := h2) (h3 := h3) (h4 := h4) (h52 := h52) (hPS := hPS)
      (h209 := h209) (hK := hOrd) (hA := hTabA)
      (hS := hSchur)
  have hA3 : S23_9_A3 D Ch := s23_9_A3_of D Ch
  have hA5 : S23_9_A5 D Ch :=
    s23_9_A5_of D Ch (h2 := h2) (h3 := h3) (h4 := h4) (h52 := h52) (h6 := h6)
      (hPS := hPS) (hSemi := hSem) (hKSU := hSU44) (hA := hTabA) (hD := hTabD)
      (hK := hOrd) (hSC := hC1Schur) (hsp := hSigma.sig1_sp)
  have hStepA : S23_9_StepA D Ch :=
    s23_9_StepA_of D Ch (h4 := h4) (h52 := h52) (hPS := hPS) (hA0 := hA0) (hA1 := hA1)
      (hASem := hASem) (hAdj := hAdjData) (hA3 := hA3) (hA4 := s23_9_A4_of D Ch) (hA5 := hA5)
      (hK462 := h462) (hKSU44 := hSU44) (hKAdj := hAdj) (hSem := hSem)
  have hB1 : S23_9_B1 D Ch := s23_9_B1_of D Ch (h8 := h8) (hA := hStepA) (hOut := hOut)
  have hB23 : S23_9_B23 D Ch :=
    s23_9_B23_of D Ch (h2 := h2) (h3 := h3) (h4 := h4) (h8 := h8) (hB1 := hB1)
      (ha := hTabA) (hd := hTabD) (hK := hOrd) (hS := hSub) (hSS := hSubS)
  have hN1 : S23_9_NotSp4SU4O6m D Ch :=
    s23_9_NotSp4SU4O6m_of D Ch (hA := hTabA) (hd := hTabD) (hG := hGen) (h4 := h4)
      (h8 := h8) (h847 := h847) (hB23 := hB23) (hK := hOrd)
      (hSC := hC1Schur)
  have hΩ : S23_9_B23Omega D Ch :=
    s23_9_B23Omega_of D Ch (h2 := h2) (h3 := h3) (h4 := h4) (h8 := h8) (hB1 := hB1)
      (ha := hTabA) (hd := hTabD) (hK := hOrd) (hS := hSub) (hSS := hSubS)
  have hC2 : S23_9_C2Emb D Ch :=
    s23_9_C2Emb_of D Ch (hA := hTabA) (hd := hTabD) (h4 := h4) (hK := hOrd) (hSO := hSchurO6)
      (h6 := h6) (h8 := h8) (hΩ := hΩ) (hσ := hSigma) (h76 := h76)
  have hN2 : S23_9_NotO6p D Ch :=
    s23_9_NotO6p_of D Ch (hA := hTabA) (h4 := h4) (hK := hOrd) (hEmb := hC2)
      (hGO := hGenO6) (hSO := hSchurO6)
  exact ⟨hPS, hB23, hN1, hN2⟩

theorem s23_9_2_full_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h209 : S20_9 D) (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch)
    (h4 : S23_4 D Ch) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h54 : S23_5_4 D Ch)
    (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch) (h8 : S23_8 D Ch) (hline : S23_5_line D Ch)
    (hKN : KNshape) (hSigma : UC6S846.SigmaStd D) (h847 : R847ThinCZ D) (hTabA : KTab23a)
    (hTabD : KTab23d) (hOrd : KOrdNatural) (hSchur : KSchurL2)
    (hSchurSL3 : KSchurSL3) (hSub : KSub23) (hSubS : KSub23Simple)
    (hNotLarge : KNotLarge23) (hGen : KGen) (hC1Schur : KSchurC1) (hGenO6 : KGenO6p)
    (hSchurO6 : KSchurO6p) (hOut : KOut23) (hSU44 : KSU44) (hAdj : KAdj)
    (h462 : UCK.K462) (h76 : F07.R76Sig D) :
    S23_9_2 D Ch := by
  obtain ⟨-, hB23, hN1, hN2⟩ :=
    s23_9_common_of D Ch (h209 := h209) (h2 := h2) (h3 := h3) (h4 := h4) (h52 := h52)
      (h53 := h53) (h54 := h54) (h6 := h6) (h71 := h71) (h8 := h8) (hSigma := hSigma)
      (h847 := h847) (hTabA := hTabA) (hTabD := hTabD) (hOrd := hOrd)
      (hSchur := hSchur) (hSub := hSub) (hSubS := hSubS) (hGen := hGen)
      (hC1Schur := hC1Schur) (hGenO6 := hGenO6) (hSchurO6 := hSchurO6) (hOut := hOut)
      (hSU44 := hSU44) (hAdj := hAdj) (h462 := h462) (h76 := h76)
  have hN3 : S23_9_NotLarge D Ch :=
    s23_9_NotLarge_of D Ch (hA := hTabA) (hd := hTabD) (h4 := h4) (h8 := h8)
      (hB23 := hB23) (hNL := hNotLarge)
  exact s23_9_2_of D Ch (hE := hE) (h207 := h207) (h2 := h2) (h3 := h3) (h4 := h4)
    (hline := hline) (hKN := hKN) (hK := hOrd) (hS := hSchur) (hS3 := hSchurSL3)
    (hN1 := hN1) (hN2 := hN2) (hN3 := hN3)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
