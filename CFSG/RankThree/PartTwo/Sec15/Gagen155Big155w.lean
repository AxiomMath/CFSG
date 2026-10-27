module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHostDefs
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigRQ
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigMain
import CFSG.RankThree.PartTwo.Sec15.Ronan155BigCases
import CFSG.RankThree.PartTwo.Sec15.Gagen155BXW
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
public import CFSG.RankThree.PartTwo.Sec15.Gagen155SplitDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xDefs
public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofCasesB
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQ0
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
public import CFSG.RankThree.PartTwo.Sec15.Item155wProofCorr
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProof
public import CFSG.RankThree.PartTwo.Sec15.Item322ScopeProofRoute
public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan155BigDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Ronan155Big

variable {G : Type} [Group G] [Finite G]

theorem false_of_end155N_of_wPBig {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h153 : Ronan153Big.Item153Big A (lB A)) (h315 : Item3_15)
    (h316 : Sec19.Item316) (hBXW : Step155BXW A c L)
    (hsubn : Step155BSubn2W A c L) (hfr : Step155FrattiniNWPBig A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hXb : Big152 X)
    (hmax : MaxT155 A X K T) (hab : Above155w A X) (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P)
    (hW : w155 A M X ≠ ⊥ → w155 A M X = delta A (lB A) (w155 A M X) ∧
      (w155 A M X ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) ∨
        Hyp315 (CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X) (CFSG.Open.pCoreOf 2 Y) ∨
        ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ CFSG.Open.pCoreOf 2 Y ∧
          (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic ∧
          w155 A M X ≤ Subgroup.normalizer (C : Set G))) : False :=
  hC.not_le (hfr h X K Y M T P hC hXb hmax hab hE hRP
    (b155_le_n155_of_end155N_of_w_big h h153 h315 h316 hBXW hsubn hC hXb hmax hab hE hW))

theorem rank3II_15_5wN_of3x_bigFr {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h152 : Item152Big A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h154 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Sec16.Item154Pi A (lB A) L')
    (h315 : Item3_15) (h316 : Sec19.Item316)
    (h322 : ∀ {H R : Subgroup G}, Hyp322 H R → CFSG.Open.pCoreOf 2 H ≤ R → IsPGroup 2 R →
      R ≠ ⊥ → ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ R ∧ (C.subgroupOf R).Characteristic ∧
        H ≤ Subgroup.normalizer (C : Set G))
    (hUp : Step155Up A c L) (hgrow : Step155GrowW A c L) (hcases : Step155CasesNWBig A c L)
    (hRQ : Step155RQNWBig A c L) (hBXW : Step155BXW A c L) (hW315 : Step155W315x A c L)
    (hsubn : Step155BSubn2W A c L) (hfr : Step155FrattiniNWPBig A c L) :
    Item155wBig A (lB A) :=
  rank3II_15_5wN_of_last_big h h152 h153 h154 h322 hUp hgrow hcases hRQ
    fun {X K Y M T P} hC hXb hmax hab hE hRP => false_of_end155N_of_wPBig h h153 h315 h316 hBXW
      hsubn hfr hC hXb hmax hab hE hRP (hW315 h X K Y M T P hC hmax hab hE hRP)

theorem item155wBigR_of_corr8Cert_bigFr
    (h152 : Item152BigR) (h153 : Ronan153Big.Item153BigR) (h154 : Item154PiR)
    (h315 : Item3_15) (h316 : Sec19.Item316) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h149 : Sec16.Item149S14)
    (h142 : Concl142S14) (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hKS155 : KS155J2CentE4) (hKSL3 : KSL3NonPiAutThree)
    (hUp : Step155UpPiNHJR) (halt : Step155GrowAltTwoFieldWR) (hYQ : Step155YQ0HypWR)
    (hPJQ : Step155PJQ0HypWR) (hY4 : Y4LThreePiNHJR) (hW315 : Step155W315xR)
    (hfr : Step155FrattiniNWPRBig) : Item155wBigR := by
  have hgrow := step155GrowWR_of h1444 h146 hbot (item154R_of_item154PiR h154)
    (step155GrowAltWR_of_two (step155GrowAltTwoWR_of_field h148 hbot h134 h48 hKSL3 halt))
  have hUp' := step155UpR_of_piR (step155UpPiR_of_nhj h148 hbot hUp)
  have hYQ' := step155YQ0WR_of h142 hYQ
  have hPJQ' := step155PJQ0WR_of h142 hPJQ
  have htwo := step155CasesTwoNHJWBigR_of_route hY4 h152 h153 hgrow h146 h1444 hbot hYQ' hPJQ'
  have hsubn := step155BSubn2WR_of h149
    (step155INormX2WR_of_rk (step155INormX2RkWR_of h148 h149))
  have hBXW := step155BXWR_of h148 h149
  exact fun G _ _ A c L hR => rank3II_15_5wN_of3x_bigFr hR.toSec14Std (h152 G A c L hR)
    (h153 G A c L hR) (fun c' L' hc' hL' => h154 G A c' L' (sec15R_of_basePoint hR hc' hL'))
    h315 h316
    (fun hyp hQR hR2 hR1 => exists_char_normal_of_hyp322TwoJ item3_22TwoJ_holds hyp hQR hR2 hR1)
    (hUp' G A c L hR) (hgrow G A c L hR)
    (step155CasesNWBig_of (h146 G A c L hR.toSec14Std) (hYQ' G A c L hR) (hPJQ' G A c L hR)
      (step155CasesTwoWBig_of_nhj (h148 G A c L hR) (hbot G A c L hR.toSec14Std)
        (htwo G A c L hR))
      (step155CasesBWR_of hKS155 G A c L hR))
    (step155RQNWBig_of (h1444 G A c L hR.toSec14Std) (h146 G A c L hR.toSec14Std)
      (hbot G A c L hR.toSec14Std) (step155RQKWBig_of (h152 G A c L hR) (h153 G A c L hR)))
    (hBXW G A c L hR) (hW315 G A c L hR) (hsubn G A c L hR) (hfr G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
