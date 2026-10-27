module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFinalChainCompose
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerOvergroupExclusion

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_singerQuotientConclusion {H : Subgroup G} {z : G} {beta : rightCosetSpace H}
    {t : G} {A : Subgroup G} {e : ℕ}
    (hqe : Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e)
    (hS : SingerQuotientConclusion H z beta t A) : False := by
  obtain ⟨-, -, -, -, -, -, hsing⟩ := hS
  obtain ⟨-, heven, he4, d, hde, F, _, _, hFcard, -, ρ, -, -, -, hscal, hcard, -⟩ :=
    hsing e hqe
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hde (by omega)
  exact Singer.not_exists_singer_overgroup_card_eq heven (hFcard.trans hqe) hd hde
    ⟨ρ.range, hscal, by rw [hcard, hqe]⟩

theorem minimalLocalFailure_pair_generated_hull_is_ambient_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (hkerAll : ∀ (beta : rightCosetSpace H) (t : G), beta ≠ rightCosetMk H 1 →
      t ∈ rightPairFlipFiber H z beta → minimalLocalFailureProperPairHull H z beta t < ⊤ →
        LinearChain.LinearPointKernelConclusion H z beta t)
    (hexclAll : ∀ (beta : rightCosetSpace H) (t : G), beta ≠ rightCosetMk H 1 →
      t ∈ rightPairFlipFiber H z beta → minimalLocalFailureProperPairHull H z beta t < ⊤ →
        ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
          UnitaryFixedModelExcludedConclusion H z u)
    (hrootAll : ∀ (beta : rightCosetSpace H) (t : G), beta ≠ rightCosetMk H 1 →
      t ∈ rightPairFlipFiber H z beta → minimalLocalFailureProperPairHull H z beta t < ⊤ →
        RootCentralizerTwoCoreConclusion H z beta t) :
    (∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 → ∀ t ∈ rightPairFlipFiber H z beta,
        minimalLocalFailureProperPairHull H z beta t = ⊤) ∧
      BasePointPairGeneration H z := by
  have hK : ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, minimalLocalFailureProperPairHull H z beta t = ⊤ := by
    intro beta hbeta t ht
    by_contra hne
    have hproper : minimalLocalFailureProperPairHull H z beta t < ⊤ := lt_of_le_of_ne le_top hne
    have hker := hkerAll beta t hbeta ht hproper
    have hexcl := hexclAll beta t hbeta ht hproper
    have hroot := hrootAll beta t hbeta ht hproper
    obtain ⟨-, ⟨e, hqe⟩, -⟩ :=
      FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
    obtain ⟨⟨A, hA⟩, -⟩ :=
      minimalLocalFailure_minimal_central_section_homocyclic_four_of_conclusions h hcomm
        hsmallerR1 hbeta ht hproper hker hexcl hroot
    exact false_of_singerQuotientConclusion hqe
      (minimalLocalFailure_small_dihedral_singer_quotient_of_conclusions h hcomm hsmallerR1 hbeta
        ht hproper hker hexcl hroot hA)
  refine ⟨hK, fun b hb t ht => ?_⟩
  have hle := sylowAssemblyProper_pair_hull_le_generated h hb ht
  rw [hK b hb t ht] at hle
  exact top_le_iff.mp hle

end CFSG.ShultStronglyClosedTI.FinalChain
