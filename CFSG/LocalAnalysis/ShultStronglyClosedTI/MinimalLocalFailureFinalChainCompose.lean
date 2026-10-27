module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCentralSection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFourSection
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureIndexDichotomy
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLargeBranch
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSingerQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootInvolutions

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.LinearChain.RootInvolutions

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_normal_two_subgroup_involution_count_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) :
    InvolutionCountConclusion H z beta t :=
  involution_count_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    (minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker)

theorem minimalLocalFailure_minimal_central_section_homocyclic_four_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) :
    CentralSectionConclusion H z beta t :=
  central_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    (minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker)

theorem minimalLocalFailure_pair_involution_inverts_central_four_section_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    FourSectionConclusion H z beta t A :=
  have hinv :=
    minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker
  four_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv
    (central_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv) hA

theorem minimalLocalFailure_two_core_central_section_index_dichotomy_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    IndexDichotomyConclusion H z beta t A :=
  have hinv :=
    minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker
  have h2 := central_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv
  index_dichotomy_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv h2 hA
    (four_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv h2 hA)

theorem minimalLocalFailure_large_two_core_branch_transfer_excluded_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    LargeBranchExcludedConclusion H z beta t A :=
  have hinv :=
    minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker
  have h2 := central_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv
  have h3 := four_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv h2 hA
  large_branch_excluded_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv
    h2 hA h3
    (index_dichotomy_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv h2
      hA h3)

theorem minimalLocalFailure_small_dihedral_singer_quotient_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hker : LinearChain.LinearPointKernelConclusion H z beta t)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hroot : RootCentralizerTwoCoreConclusion H z beta t) {A : Subgroup G}
    (hA : IsMinimalCentralSection H (minimalLocalFailurePairActionPointHull H z)
      (TwoCoreGrowth.pointTwoCoreImage H) A) :
    SingerQuotientConclusion H z beta t A :=
  have hinv :=
    minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hker
  have h2 := central_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv
  have h3 := four_section_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv h2 hA
  have h4 := index_dichotomy_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
    hinv h2 hA h3
  singer_quotient_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot hinv h2 hA
    h3 h4
    (large_branch_excluded_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hker hexcl hroot
      hinv h2 hA h3 h4)

end CFSG.ShultStronglyClosedTI.FinalChain
