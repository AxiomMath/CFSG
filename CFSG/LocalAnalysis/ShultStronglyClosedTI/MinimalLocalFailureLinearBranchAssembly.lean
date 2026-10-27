module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiExcluded
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernelOddCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreTrivialPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthNode
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootInvolutions
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootQuotientClasses
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairTwoCoreNontrivial
public import CFSG.CharacterTheory.DihedralTIFusion.SuzukiFusion

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearBranchAssembly

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.LinearChain
open LinearChain.RootInvolutions LinearChain.RootQuotientClasses

variable {G : Type} [Group G] [Finite G]

theorem linear_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k) :=
  (SuzukiExclusion.minimalLocalFailure_proper_pair_suzuki_excluded_of_conclusions h hcomm
    hsmallerR1 hbeta ht hproper (proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper)
    hexcl).1.choose_spec.2.2

theorem pointKernel_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    LinearPointKernelConclusion H z beta t :=
  minimalLocalFailure_linear_point_kernel_and_odd_centralizers_of_conclusions h hcomm hsmallerR1
    hbeta ht hproper (linear_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl) hexcl

theorem rootInvolutions_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    FinalChain.RootCentralizerInvolutionsConclusion H z beta t :=
  minimalLocalFailure_root_centralizer_involutions_have_two_fixed_points_of_conclusions
    h hcomm hsmallerR1 hbeta ht hproper
    (pointKernel_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)

theorem oddCoreFree_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    RootCentralizerOddCoreFreeConclusion H z :=
  minimalLocalFailure_linear_point_kernel_odd_core_free_quotient_of_conclusions h hcomm hsmallerR1
    hbeta ht hproper (linear_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl) hexcl

theorem trivialPair_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    TrivialPairTwoCoreConclusion H z beta t :=
  minimalLocalFailure_trivial_pair_two_core_forces_root_two_core_of_conclusions h hcomm hsmallerR1
    hbeta ht hproper (linear_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl) hexcl
    (TwoCoreGrowthNode.minimalLocalFailure_two_core_involution_subgroup_growth_of_conclusions h
      hcomm hsmallerR1 hbeta ht hproper
      (pointKernel_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl))

theorem quotientClasses_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    RootQuotientInvolutionClassesConclusion H z beta :=
  minimalLocalFailure_linear_root_quotient_multiple_involution_classes_of_conclusions
    h hcomm hsmallerR1 hbeta ht hproper hexcl
    (pointKernel_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)

theorem dihedral_fusion : ∀ (E : Type) [Group E] [Finite E] (W : Subgroup E), IsCyclic W →
    Odd (Nat.card W) → 3 ≤ Nat.card W → ∀ (u : E), u ∉ W → orderOf u = 2 →
    (∀ w ∈ W, u⁻¹ * w * u = w⁻¹) →
    (∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.centralizer (W₀ : Set E) = W) →
    (∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ →
      Subgroup.normalizer (W₀ : Set E) = W ⊔ Subgroup.zpowers u) →
    (∀ K : Subgroup E, K.Normal → K ≠ ⊥ → u ∈ K) →
    (∀ t : E, orderOf t = 2 → IsConj t u) ∧
      ∃! c : ConjClasses E, ∃ t : E, orderOf t = 2 ∧ ConjClasses.mk t = c :=
  fun _ _ _ _ hWc hWo hW3 _ huW hu hinv hc hn hK =>
    CFSG.DihedralTIFusion.suzuki_odd_cyclic_dihedral_involution_fusion hWc hWo hW3 huW hu hinv
      hc hn hK

theorem rootTwoCore_of_unitaryExcluded
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hsetup : RootQuotientCharacterSetupConclusion H z beta t)
    (hforces : NontrivialPairTwoCoreConclusion H z beta t) :
    FinalChain.RootCentralizerTwoCoreConclusion H z beta t :=
  hforces
      (minimalLocalFailure_pair_centralizer_two_core_nontrivial_of_conclusions h hcomm hsmallerR1
          hbeta ht hproper (linear_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)
          hexcl hsetup
          (quotientClasses_of_unitaryExcluded h hcomm hsmallerR1 hbeta ht hproper hexcl)
          dihedral_fusion)

end CFSG.ShultStronglyClosedTI.LinearBranchAssembly
