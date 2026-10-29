module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Seven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.RankThree.PartOne.Q1327T.Defs
import CFSG.RankThree.PartOne.Q1327T.ThetaLift
import CFSG.RankThree.PartTwo.KFacts.KS116Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115
import CFSG.RankThree.PartTwo.Sec11.Item116H3Main
import CFSG.RankThree.PartTwo.Sec11.Item116R1CD
import CFSG.RankThree.PartTwo.Sec11.Item116R2NoHoles
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.LSSolvableProof
import CFSG.RankThree.PartTwo.Sec11.Transitivity
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.RankThree.PartTwo.Sec4.T444.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace C163

theorem exists_notMem_normalizer_of_s15_ne_one {M V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hs : s15 M V₀ V hV L ≠ 1) :
    ∃ φ ∈ Mbar M V₀ V hV,
      φ ∉ normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  by_contra hcon
  push Not at hcon
  apply hs
  have hset : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} =
      {barSub V₀ V hV L} := by
    apply le_antisymm
    · rintro X ⟨φ, hφ, rfl⟩
      rw [Set.mem_singleton_iff]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hcon φ hφ)
    · intro X hX
      rw [Set.mem_singleton_iff] at hX
      subst hX
      exact ⟨1, (Mbar M V₀ V hV).one_mem, by ext x; simp⟩
  unfold s15
  rw [hset, Set.ncard_singleton]

end C163

theorem r16_3_2_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h119 : F11.R119 D) : R16_3_2 D := by
  intro V₀ V L hV hSet _ hc hΩ
  obtain ⟨t, -, -, -, -, hW⟩ := hc
  obtain ⟨K, hK, g, hg, hKg, hL, hK8, hT⟩ := C163.exists_tensor_of_isOmegaPlus_eight hW hΩ
  unfold Case163_2
  refine ⟨hΩ, natOmegaPlus_of_natTensor (by norm_num) hT, ?_⟩
  by_contra hs
  obtain ⟨φ, hφ, hφN⟩ := C163.exists_notMem_normalizer_of_s15_ne_one hV hs
  have hcomm := (hW.2.1 φ hφ hφN).1
  rw [hL] at hcomm
  have h7 : 7 ∈ D.sig :=
    C163.seven_mem_sig D hSg h127 h119 hSet.hyp16.hyp125 hV hK hK8 hg hφ hKg hcomm
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 254016 :=
    (Om8Excl.card_isOmegaPlus_four (by norm_num) hΩ).trans (by norm_num)
  have hLA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hSet.hyp151.le
  have hV₀ : Nat.card V₀ < 7 := by
    have := c23_card_v0_le_four D hSet.hyp16
    omega
  have hU : ∀ w ∈ V, w ≠ 1 → UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
    intro w hw _
    obtain ⟨E, hEM, hEp, hEc, hEw⟩ :=
      C163.exists_noncyclic_fix hW hLA hcard hT hφ hφN (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩))
    obtain ⟨P, hPle, hPp, hPc⟩ :=
      C163.exists_noncyclic_le_centralizer hV Nat.prime_seven hV₀ hw hEM hEp hEc hEw
    exact UC22.uc22p22u_uniqueMax_mono D hPle inf_le_left
      (h61 7 h7 P (hPle.trans inf_le_left) hPp hPc)
  exact r129_1_of_r127 D h127 V₀ V hSet.hyp16.hyp125
    (s15_FiveTen_isTI_of_uniqueMax D hV hSet.hyp16.hyp125.pairFacts.le_normalizer hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
