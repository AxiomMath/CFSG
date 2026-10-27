module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcluded
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHulls

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_pair_involution_unitary_fixed_model_excluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
    (∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) ≠ q ^ 3 + 1) ∧
    ∃ i : ℕ, (i = 1 ∨ i = 2) ∧ ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      Nat.card (rightFixedSet H u) = q ^ i + 1 ∧
        Nat.card (rightCosetSpace H) = (q ^ i + 1) * (q ^ i * (q - 1) + 1) :=
  minimalLocalFailure_pair_involution_unitary_fixed_model_excluded_of_hulls h hcomm hsmallerR1
    hbeta ht hproper fun _ huB hu hfix =>
      UnitaryHulls.minimalLocalFailure_unitary_fixed_hulls_generate h hcomm hsmallerR1 hbeta ht
        hproper huB hu hfix

end CFSG.ShultStronglyClosedTI.UnitaryExcluded

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G] [Finite G]

theorem unitaryFixedModelExcludedConclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u :=
  unitaryFixedModelExcludedConclusion_of_hulls h hcomm hsmallerR1 hbeta ht hproper
    fun _ huB hu hfix =>
      UnitaryHulls.minimalLocalFailure_unitary_fixed_hulls_generate h hcomm hsmallerR1 hbeta ht
        hproper huB hu hfix

end CFSG.ShultStronglyClosedTI.ProperPairModel
