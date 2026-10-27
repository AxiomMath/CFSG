module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeLocalIndex
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizer

public section

namespace CFSG.ShultStronglyClosedTI.SuzukiPairPrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem suzuki_degree_identity {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) - 1 = q ^ 3 * (q ^ 2 - q + 1) := by
  rw [CoprimePrime.suzuki_factor_eq hq]
  obtain ⟨d, rfl⟩ : ∃ d, q = d + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h : ((d + 1) ^ 2 + 1) * ((d + 1) ^ 2 * d + 1) =
      (d + 1) ^ 3 * ((d + 1) * d + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel]

omit [Finite G] in
theorem baseOrbit_top (H : Subgroup G) : CyclicSemiregular.baseOrbit H ⊤ = Set.univ := by
  ext ω
  refine ⟨fun _ => Set.mem_univ ω, fun _ => ?_⟩
  obtain ⟨g, rfl⟩ := PairInvolutionFixedField.exists_rightCosetMk ω
  exact ⟨g, Subgroup.mem_top g, by rw [rightCosetTranslate_mk, one_mul]⟩

theorem suzuki_pair_degree
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hreg : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      RegularComplementConclusion H z beta t u)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* CFSG.Blueprint.suzukiGroup m k)) :
    let B := pairPointStabilizer H beta
    let Q := minimalLocalFailurePairActionPointHull H z
    Nat.card (rightCosetSpace H) - 1 = Nat.card Q ^ 3 * (Nat.card Q ^ 2 - Nat.card Q + 1) ∧
      B.relIndex H = Nat.card (rightCosetSpace H) - 1 := by
  intro B Q
  obtain ⟨u, huB, hu⟩ := hBinv
  obtain ⟨-, hfix, -⟩ := hreg u huB hu
  obtain ⟨T, -, -, -, -, -, -, -, -, -, -, -, hSuz, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hΔ⟩ := hSuz hSz
  obtain ⟨i, hi, hFix, hΩ⟩ := hexcl u huB hu
  have hFix' : Nat.card (rightFixedSet H u) = Nat.card Q ^ i + 1 := hFix
  have hΩ' : Nat.card (rightCosetSpace H) =
      (Nat.card Q ^ i + 1) * (Nat.card Q ^ i * (Nat.card Q - 1) + 1) := hΩ
  obtain ⟨-, hQ4, -⟩ := CyclicSemiregular.proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht
    hproper
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hFix2 : Nat.card (rightFixedSet H u) = Nat.card Q ^ 2 + 1 := by
    rw [hfix]
    exact hΔ
  have hi2 : i = 2 := by
    rcases hi with rfl | rfl
    · exfalso
      rw [hFix2, pow_one] at hFix'
      have h1 : Nat.card Q ^ 2 = Nat.card Q := by omega
      nlinarith
    · rfl
  subst hi2
  have hdeg : Nat.card (rightCosetSpace H) - 1 =
      Nat.card Q ^ 3 * (Nat.card Q ^ 2 - Nat.card Q + 1) := by
    rw [hΩ']
    exact suzuki_degree_identity (by omega)
  refine ⟨hdeg, ?_⟩
  have h2 := CyclicSemiregular.proper_pair_two_transitive h hcomm hsmallerR1 hbeta ht hproper
  have hβ : beta ∈ CyclicSemiregular.baseOrbit H ⊤ := by
    rw [baseOrbit_top]
    exact Set.mem_univ _
  have hidx := CoprimePrime.pair_relIndex_of_two_transitive H ⊤ hbeta hβ
    (fun a _ b _ c _ d _ hab hcd => by
      obtain ⟨g, hg⟩ := h2 a b c d hab hcd
      exact ⟨g, Subgroup.mem_top g, hg⟩)
  rw [inf_top_eq, inf_top_eq, baseOrbit_top, Nat.card_univ] at hidx
  exact hidx

end CFSG.ShultStronglyClosedTI.SuzukiPairPrime
