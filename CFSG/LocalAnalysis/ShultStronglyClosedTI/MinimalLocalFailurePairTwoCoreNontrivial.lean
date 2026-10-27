module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLinearPointKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootTwoCoreStatement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem minimalLocalFailure_pair_centralizer_two_core_nontrivial_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hsetup : RootQuotientCharacterSetupConclusion H z beta t)
    (hclasses : RootQuotientInvolutionClassesConclusion H z beta)
    (hfusion : ∀ (E : Type) [Group E] [Finite E] (W : Subgroup E), IsCyclic W →
      Odd (Nat.card W) → 3 ≤ Nat.card W → ∀ (u : E), u ∉ W → orderOf u = 2 →
      (∀ w ∈ W, u⁻¹ * w * u = w⁻¹) →
      (∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ → Subgroup.centralizer (W₀ : Set E) = W) →
      (∀ W₀ : Subgroup E, W₀ ≤ W → W₀ ≠ ⊥ →
        Subgroup.normalizer (W₀ : Set E) = W ⊔ Subgroup.zpowers u) →
      (∀ K : Subgroup E, K.Normal → K ≠ ⊥ → u ∈ K) →
      (∀ t : E, orderOf t = 2 → IsConj t u) ∧
        ∃! c : ConjClasses E, ∃ t : E, orderOf t = 2 ∧ ConjClasses.mk t = c) :
    PairCentralizerTwoCoreNontrivialConclusion H z beta t := by
  unfold PairCentralizerTwoCoreNontrivialConclusion
  intro hJ2
  obtain ⟨-, -, -, -, -, hJeq, -, -, hJQ, -, -, hinv, -⟩ :=
    minimalLocalFailure_linear_point_kernel_and_odd_centralizers_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hlin hexcl
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper
  have huJ := hinv u huB hu
  have huC : u ∈ H ⊓ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) :=
    ⟨pairPointStabilizer_le_point H beta huB, hJQ huJ⟩
  obtain ⟨hQCn, -, -, hsetupu⟩ := hsetup hJ2
  obtain ⟨W, -, -, hWodd, hW3, hWbarcyc, hWbarcard, hord, huW, hinvert, hcn, hnorm⟩ :=
    hsetupu ⟨u, huC⟩ huJ hu
  obtain ⟨-, hQCn', a, b, ha, hb, hab⟩ := hclasses
  have hone := (hfusion _ _ hWbarcyc (hWbarcard ▸ hWodd) (hWbarcard ▸ hW3) _ huW hord hinvert
    (fun W₀ h1 h2 => (hcn W₀ h1 h2).1) (fun W₀ h1 h2 => (hcn W₀ h1 h2).2) hnorm).1
  exact hab ((hone a ha).trans (hone b hb).symm)

end CFSG.ShultStronglyClosedTI.LinearChain
