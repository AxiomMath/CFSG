module

public import Certificates.Certificate148000
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.VecOvergroupModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.LSubAlpha
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigComponents
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.CardMapSimple
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockProperSupportOdd
public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilyCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofONGen
public import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofONPoint
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ONProofType
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.KF148SigONE27Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigReduction
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroupCentralizer
public import CFSG.RankThree.PartTwo.Sec6.Item612
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.PresentedWords
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate2201
public import Certificates.Certificate2202
public import Certificates.Certificate2326
public import Certificates.Certificate43
public import Certificates.Certificate8026Base
public import Certificates.Certificate8166
public import Certificates.Certificate8169
public import Certificates.Certificate9124

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native
open scoped commutatorElement
open CFSG.RankThree.Native.ONTriple
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

local notation "LSubK" => CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.LSub

section Fix


set_option linter.unusedSectionVars false

theorem LSub_zero_fix {k : ℕ} (hk : k < 9) : ∃ w : Fin nPts, ∀ t ∈ LSubK 0 k, phiJ t • w = w :=
  Certificates.certificate148000 k hk

theorem card_LSub_zero_map {k : ℕ} (hk : k < 9) :
    Nat.card ((LSubK 0 k).map phiJ) = 1876896 := by
  haveI := isSimpleGroup_LSub (j := 0) (by norm_num) hk
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving.card_map_of_isSimpleGroup phiJ ?_,
    card_LSub (by norm_num) hk]
  intro hle
  have h1 : Nat.card (LSubK 0 k) ∣ Nat.card (Subgroup.zpowers zG) :=
    Subgroup.card_dvd_of_le (hle.trans ker_phiJ.le)
  rw [Nat.card_zpowers, orderOf_zG', card_LSub (by norm_num) hk] at h1
  norm_num at h1

theorem isPerfect_of_isSimpleGroup' {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (h : ∃ a b : Q, a * b ≠ b * a) : Group.IsPerfect Q := by
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup Q) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hm : ⁅a, b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [commutator_def]
    exact ht

theorem exists_noncomm_of_card' {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hc : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := fun a b => h a b }
  exact hc (IsSimpleGroup.prime_card (α := Q))

theorem isPerfect_LSub_zero {k : ℕ} (hk : k < 9) : Group.IsPerfect (LSubK 0 k) := by
  haveI := isSimpleGroup_LSub (j := 0) (by norm_num) hk
  apply isPerfect_of_isSimpleGroup'
  apply exists_noncomm_of_card'
  rw [card_LSub (by norm_num) hk]
  norm_num


theorem le_normalizer_or_eq_top_LSub_zero {k : ℕ} (hk : k < 9) {Y : Subgroup GM}
    (hY : LSubK 0 k ≤ Y) :
    Y ≤ Subgroup.normalizer (LSubK 0 k : Set GM) ∨ Y = ⊤ := by
  haveI := isPerfect_LSub_zero hk
  obtain ⟨w, hw⟩ := LSub_zero_fix hk
  exact le_normalizer_or_eq_top_of_vec (T := LSubK 0 k) (w := w) hw (card_LSub_zero_map hk) hY


theorem l37OvergroupTransfer_holds :
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig.L37OvergroupTransfer :=
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig.l37OvergroupTransfer_of_lSub
    fun j hj k hk Y hY => by
      interval_cases j
      · exact le_normalizer_or_eq_top_LSub_zero hk hY
      · exact le_normalizer_or_eq_top_LSub_one hk hY

end Fix

end CFSG.RankThree.PartTwo.Sec4.Ronan148H
