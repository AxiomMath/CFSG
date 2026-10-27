module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Rows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Aset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritS2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154PStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UThree
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD556
public import CFSG.Quasithin.Vol2.Ch11SecD556I
public import CFSG.Quasithin.Vol2.Ch11SecD557A
public import CFSG.Quasithin.Vol2.Ch11SecFCase2
public import CFSG.Quasithin.Vol2.Ch11SecFKL1b
public import CFSG.Quasithin.Vol2.Ch11SecFQ3
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.Q1327T.Defs
public import CFSG.RankThree.PartOne.Q1327T.ThetaLift
public import CFSG.RankThree.PartTwo.KFacts.KS116Proof
public import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_v1_inCalV (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥) :
    InCalV D.M (v1Sub D.M ⊥ V h.hyp151.isElemAbelian L) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hZpre := s16h_wSub_inf_centralizer_eq_preTil D h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hZ
    have hZle : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) ≤ v1Sub D.M ⊥ V hV L := by
      rw [v1Sub_of_eq_bot D.M ⊥ V hV L rfl]
      refine le_trans ?_ (le_iSup (fun m : D.M =>
        conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) (m : G)) 1)
      rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
    have hZbot : wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
      le_bot_iff.1 (hZle.trans hbot.le)
    have hmapbot : imgTil (⊥ : Subgroup G) V hV (⊥ : Subgroup G) = ⊥ :=
      s15_Core_imgTil_eq_bot_of_le (V₀ := ⊥) (V := V) (U := ⊥) hV bot_le
    have h1 := congrArg (imgTil (⊥ : Subgroup G) V hV) (hZpre.symm.trans hZbot)
    rw [imgTil_preTil, hmapbot] at h1
    exact h1
  · exact (s15_Infra_v1Sub_le h125 hV).trans h125.pairFacts.le_M
  · exact s15_Infra_le_normalizer_v1Sub h125 hV
  · exact hV.mono (s15_Infra_v1Sub_le h125 hV)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
