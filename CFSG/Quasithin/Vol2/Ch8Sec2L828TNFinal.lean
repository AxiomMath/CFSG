module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNAssem
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN5
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN1aGlue
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN2aMain
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNKfacts
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNRank
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNSolv
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSixB3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829P7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H13.L828N
open scoped IsMulCommutative

private theorem pCore_two_le_solvableRadical_828N (X : Type) [Group X] [Finite X] :
    CFSG.pCore 2 X ≤ CFSG.solvableRadical X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hp : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 X) := hp.isNilpotent
  exact le_sSup ⟨inferInstance, inferInstance⟩

theorem stmt8_2_9_three_of (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827) (h822 : Stmt8_2_2)
    (hMB0 : MB0_828) (hMB2 : MB2_828) (hMB3 : MB3_828) (hMB4 : MB4_828)
    (hSyl : Sylow822VB_828) (hE22 : E2.E22StatementC) (hE3 : E3_828) (hE4 : E4_828) :
    Stmt8_2_9_three := by
  intro G _ _ T L I hyp h731 h821 hc hrow hr
  classical
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  have hP7 : Stmt8_2_2P7 := stmt8_2_2P7_of h37 h38 h39 h3228 h325 h331 hC58 h317 h711n
  obtain ⟨H, h, k, hH, hh, hC⟩ := exists_concl822_of_82 h822 hyp h731 h821 hrow
  have c := s828_ctx hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB3 hSyl hyp h731
    h821 hrow hH hh hC
  obtain ⟨K, hLUK, hKN, hNK, hq, hcc⟩ :=
    s828N_K h37 h38 h39 hmod h711n hcard hLU h825 h827 hyp h731 h821 hrow hH hh hC
  have hD5 := s828_six_a hMB2 hLU hcard hyp hrow hr c
  have hAp : IsPGroup 2 ↥(ch82A (fsuV T I) h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hX6 := (hlu82_82 hLU hcard hrow c.hL0 c.hV c.hLN c.hC5 c.hAN c.hAL hAp c.hAe).2.2.1 hr
  have hKf := s828N_Kfacts c hX6 (s828N_card_U c hr) hLUK hKN hq hcc
  have hrH := s828N_pRank hmod (p := 5) (hp := ⟨by norm_num⟩) (by norm_num) hyp hH hC c.hC5
    hKN hNK hcc hKf.2.2.1
  have hHIT : H = ch82I (fsuV T I) h ⊔ T := hrH.1
  have hr5 : CFSG.Open.pRank 5 H ≤ 1 := hrH.2
  have hPV : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hP7 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hSixB := step828SixB_holds hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB2 hMB3
    hMB4 hSyl G T L I hyp h731 h821 hc hrow H h k hH hh hC hr hD5
  by_cases hsolv : Group.IsSolvable ↥H
  · have hY := s828N_solv hmod hyp hH hC c.hL0 c.hTL hD5 hr5 hsolv
    have hT : QuasithinUnique.IsSylowTwoOf T H :=
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
    have hTI := T_normalizes_ch82I_829 hT c.hVT c.hTV hh c.hhI hPV hY
    exact hSixB (hTI.trans (normalizer_le_normalizer_oTwoUpper _))
  · obtain ⟨hmin, hsq, -, -⟩ := setting_822 h37 h38 h39 h3228 h325 h331 hC58 h317 hyp c.hTL hH
    obtain ⟨Y, hYc, hHY, hYq, hYC, hSz⟩ := s828N_Y hE22 hE4 hyp c hmin hsq hsolv hHIT hKN hNK hcc
      hKf.2.2.2 hKf.2.1
    have hTH : T ≤ H := hHIT ▸ le_sup_right
    rcases hSz with ⟨hJ, ⟨t, htT, hne, -⟩, n, hn, hsz⟩ | ⟨hTN, -, n, hn, hsz⟩
    · refine s828N_case1a_false (hTH htT) hYc hne ?_ hsz hr5
      rw [hJ, CFSG.openPCoreOf_subgroupOf]
      exact pCore_two_le_solvableRadical_828N ↥H
    · exact s828N_case2a_false hE3 c hmin hPV hHIT hHY hTN hsz hD5

end CFSG.Quasithin.H13
