module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearBranchAssembly
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedNode
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCharacterSetup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairHullAmbient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairStatements

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.PairGeneration

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.LinearChain
open CFSG.ShultStronglyClosedTI.LinearBranchAssembly
open LinearChain.CharacterSetup LinearChain.NontrivialTwoCore

variable {G : Type} [Group G] [Finite G]

theorem rootTwoCore_of_least_failure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    FinalChain.RootCentralizerTwoCoreConclusion H z beta t := by
  have hexcl := unitaryFixedModelExcludedConclusion h hcomm hsmallerR1 hbeta ht hproper
  have hker := pointKernel_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl
  refine rootTwoCore_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl ?_ ?_
  · exact minimalLocalFailure_root_centralizer_quotient_character_setup_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper
      (linear_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl) hexcl hker
      (oddCoreFree_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)
      (trivialPair_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)
  · exact minimalLocalFailure_nontrivial_pair_two_core_forces_two_centralizer_of_conclusions
      h hcomm hsmallerR1 hbeta ht hproper hexcl hker
      (rootInvolutions_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)

theorem minimalLocalFailure_pair_generated_hull_is_ambient
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    minimalLocalFailureProperPairHull H z beta t = ⊤ ∧
      (Subgroup.zpowers z ⊔ Subgroup.zpowers t) ⊔ pairOddCore H beta = ⊤ := by
  have hall := FinalChain.minimalLocalFailure_pair_generated_hull_is_ambient_of_conclusions h hcomm
    hsmallerR1
    (fun _ _ hβ hβt hp => pointKernel_of_unitaryExcluded h hcomm hsmallerR1 hβ hβt hp
      (unitaryFixedModelExcludedConclusion h hcomm hsmallerR1 hβ hβt hp))
    (fun _ _ hβ hβt hp => unitaryFixedModelExcludedConclusion h hcomm hsmallerR1 hβ hβt hp)
    (fun _ _ hβ hβt hp => rootTwoCore_of_least_failure h hcomm hsmallerR1 hβ hβt hp)
  exact ⟨hall.1 beta hbeta t ht, hall.2 beta hbeta t ht⟩

theorem pair_generated_hull_eq_top
    (G : Type) [Group G] [Finite G] (H : Subgroup G) (z : G)
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    minimalLocalFailureProperPairHull H z beta t = ⊤ :=
  (minimalLocalFailure_pair_generated_hull_is_ambient h (properStrongEmbeddingCommutingImages G)
    (smallerR1Full_of_bender G) hbeta ht).1

theorem pairGenerationTheorem
    (G : Type) [Group G] [Finite G] :
    CFSG.ProperTwoGeneratedCore.HighRankPair.PairGenerationTheorem G := fun _ _ h _ hbeta _ ht =>
  (minimalLocalFailure_pair_generated_hull_is_ambient h (properStrongEmbeddingCommutingImages G)
    (smallerR1Full_of_bender G) hbeta ht).2

end CFSG.ShultStronglyClosedTI.PairGeneration
