module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCountBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePointIndexTwo
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSingerQuotientRep

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem singer_quotient_of_conclusions
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t)
    (hinv : RootCentralizerInvolutionsConclusion H z beta t)
    (h2 : CentralSectionConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A)
    (h3 : FourSectionConclusion H z beta t A) (h4 : IndexDichotomyConclusion H z beta t A)
    (h5 : LargeBranchExcludedConclusion H z beta t A) :
    SingerQuotientConclusion H z beta t A := by
  have hyps : FinalHyps H z beta t :=
    ⟨h, hcomm, hsmallerR1, hbeta, ht, hproper, hker, hexcl, hroot, hinv⟩
  obtain ⟨hQH, hQn, -, hQ4, -, hBH, hXB, -⟩ := hyps.point_data
  obtain ⟨-, hM, hJB, hJM, -, -, -, -, -, -, hBidx⟩ := hyps.core_data
  obtain ⟨u, hu2, hJu, huinv, -⟩ := h3
  obtain ⟨-, hcent⟩ := h2
  obtain ⟨hAJ, hAcard, hAiso, -⟩ := hcent A hA
  obtain ⟨hAH, hAn, -, hAM, -⟩ := hA
  obtain ⟨hrel, -⟩ := h4
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨k₀, _, _, hk₀, φ, ι, hιker, hιact, hιX⟩, -⟩ := hker
  have hHN : H ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  obtain ⟨hJz, hJcard, hMeq, hMcard⟩ := SingerQuotient.two_core_eq_sup hu2 hJu hAJ hAM hJM
    (hrel.resolve_right h5) ((hJB.trans hBH).trans hHN)
  have huH : u ∈ H := hBH (hJB (hJz ▸ Subgroup.mem_zpowers u))
  dsimp only [SingerQuotientConclusion]
  refine ⟨u, hu2, hJu, hJz ▸ hMeq, hJz ▸ hAJ, huinv, fun e hqe => ?_⟩
  obtain ⟨ψ⟩ := hAiso e hqe
  have he2 : 2 ≤ e := by
    have h4e : 2 ^ 2 ≤ 2 ^ e := by
      rw [← hqe]
      exact hQ4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4e
  have heven : Even e := SingerQuotient.even_of_inv hAH hAn
    (minimalLocalFailure_point_stabilizer_no_index_two_subgroup h) huH huinv ψ
  have : CharP k₀ 2 := LinearModel.charP_two_of_card (hk₀.trans hqe)
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  obtain ⟨d, hde, ρ, hρker, hρact, hρX, hρS, hρcard, hρcore, hne2⟩ :=
    SingerQuotient.exists_singer_rep hQH hQn hBH hXB hJB hM
      (TwoCoreGrowth.pointTwoCoreImage_subgroupOf H) (by omega) hqe hBidx hJcard
      (by rw [hMcard, hAcard]) hk₀ φ ι hιker hιact hιX
  have he4 : 4 ≤ e := by
    obtain ⟨r, hr⟩ := heven
    omega
  exact ⟨⟨ψ⟩, heven, he4, d, hde, k₀, inferInstance, inferInstance, hk₀, φ, ρ, hρker, hρact,
    hρX, hρS, hρcard, hρcore⟩

end CFSG.ShultStronglyClosedTI.FinalChain
