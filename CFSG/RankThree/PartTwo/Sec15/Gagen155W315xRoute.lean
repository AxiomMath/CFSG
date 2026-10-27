module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155SplitRoute
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXW
public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofRQK
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofCasesB
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQ0
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofA5
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProof
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofRoute

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof155R2

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_5wN_of3x {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h152 : Item152 A (lB A)) (h153 : Item153Main A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h315 : Item3_15) (h316 : Sec19.Item316)
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNW A c L)
    (hRQ : Step155RQNW A c L) (hBXW : Step155BXW A c L) (hW315 : Step155W315x A c L)
    (hsubn : Step155BSubn2W A c L) (hfr : Step155FrattiniNWP A c L) : Item155w A (lB A) :=
  rank3II_15_5wN_of_last h h152 h153 h154 h322 hUp hgrow hcases hRQ
    fun {X K Y M T P} hC hmax hab hE hRP => false_of_end155N_of_wP h h153 h315 h316 hBXW hsubn hfr
      hC hmax hab hE hRP (hW315 h X K Y M T P hC hmax hab hE hRP)

theorem item155wR_of_corr8Cert
    (h152 : Item152R) (h153 : Item153MainR) (h154 : Item154PiR)
    (h315 : Item3_15) (h316 : Sec19.Item316) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKS155 : KS155J2CentE4) (hKSL3 : KSL3NonPiAutThree)
    (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR)
    (hPJQ : Step155PJQ0HypWR) (htwo : Step155CasesTwoNHJWR) (hW315 : Step155W315xR)
    (hfr : Step155FrattiniNWPR) : Item155wR := by
  have hgrow := step155GrowWR_of h1444 h146 hbot (item154R_of_item154PiR h154)
    (step155GrowAltWR_of_two (step155GrowAltTwoWR_of_field h148 hbot h134 h48 hKSL3 halt))
  have hUp' := step155UpR_of_piR (step155UpPiR_of_nhj h148 hbot hUp)
  have hcases := step155CasesNWR_of h146 (step155YQ0WR_of h142 hYQ) (step155PJQ0WR_of h142 hPJQ)
    (step155CasesTwoWR_of_nhj h148 hbot htwo) (step155CasesBWR_of hKS155)
  have hsubn := step155BSubn2WR_of h149
    (step155INormX2WR_of_rk (step155INormX2RkWR_of h148 h149))
  have hBXW := step155BXWR_of h148 h149
  exact fun G _ _ A c L hR => rank3II_15_5wN_of3x hR.toSec14Std (h152 G A c L hR)
    (h153 G A c L hR) (fun c' L' hc' hL' => h154 G A c' L' (sec15R_of_basePoint hR hc' hL'))
    h315 h316
    (fun hyp hQR hR2 hR1 => exists_char_normal_of_hyp322TwoJ item3_22TwoJ_holds hyp hQR hR2 hR1)
    (hUp' G A c L hR) (hgrow G A c L hR) (hcases G A c L hR)
    (step155RQNW_of (h1444 G A c L hR.toSec14Std) (h146 G A c L hR.toSec14Std)
      (hbot G A c L hR.toSec14Std) (step155RQKW_of (h152 G A c L hR) (h153 G A c L hR)))
    (hBXW G A c L hR) (hW315 G A c L hR) (hsubn G A c L hR) (hfr G A c L hR)

theorem item156R_of_steps155w8Cert
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h154 : Item154PiR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (hc142 : Concl142S14) (hKS155 : KS155J2CentE4)
    (hKSL3 : KSL3NonPiAutThree) (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR)
    (hYQ : Step155YQ0HypWR) (hPJQ : Step155PJQ0HypWR) (htwo : Step155CasesTwoNHJWR)
    (hW315 : Step155W315xR) (hfr : Step155FrattiniNWPR) : Item156R := by
  have h153 : Item153MainR := item153MainR_of_char h148 h149 h152
    (claim153CharR_of_twin h315 h316 h149 (claim153TwinR_of_items h148 h149 h152) hpush)
  exact item156R_of_twin5 h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush
    (item155wR_of_corr8Cert h152 h153 h154 h315 h316 h1444 h146 hbot h149 hc142 h148 h134 h48
      hKS155 hKSL3 hUp halt hYQ hPJQ htwo hW315 hfr) hrest

theorem item155R_of_steps155w8Cert
    (h148 : Item148R) (h152 : Item152R) (h149 : Sec16.Item149S14) (h315 : Item3_15)
    (h316 : Sec19.Item316) (h1411 : Item1411_1R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14) (h154 : Item154PiR) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (hpush : Step153CharPush)
    (hrest : Step156CQA5DFaithR) (hc142 : Concl142S14) (hKS155 : KS155J2CentE4)
    (hKSL3 : KSL3NonPiAutThree) (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR)
    (hYQ : Step155YQ0HypWR) (hPJQ : Step155PJQ0HypWR) (htwo : Step155CasesTwoNHJWR)
    (hW315 : Step155W315xR) (hfr : Step155FrattiniNWPR) : Item155R := by
  have h153 : Item153MainR := item153MainR_of_char h148 h149 h152
    (claim153CharR_of_twin h315 h316 h149 (claim153TwinR_of_items h148 h149 h152) hpush)
  exact item155R_of_twin5 h148 h152 h149 h315 h316 h1411 h134 h48 h142 hpush
    (item155wR_of_corr8Cert h152 h153 h154 h315 h316 h1444 h146 hbot h149 hc142 h148 h134 h48
      hKS155 hKSL3 hUp halt hYQ hPJQ htwo hW315 hfr) hrest

end CFSG.RankThree.PartTwo.Sec15
