module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPointGroupKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexFixedOrbit
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexIntersection

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pair_stabilizer_relIndex_eq_card_sub_one (H : Subgroup G) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1)
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) :
    (pairPointStabilizer H beta).relIndex H = Nat.card (rightCosetSpace H) - 1 := by
  have hmul := pointRightCosetMul_eq_translate (H := H)
  have hidx := point_centralizer_index_of_full_offBase_orbit H H le_rfl 1 H.one_mem
    (fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp))
    beta hbeta (by rw [hmul, rightCosetTranslate_one]) (fun ω _ hω => by
      obtain ⟨g, hgα, hgβ⟩ := htwo (rightCosetMk H 1) beta (rightCosetMk H 1) ω hbeta.symm
        (Ne.symm hω)
      exact ⟨⟨g, (PairInvolutionFixedField.translate_base_iff H g).mp hgα⟩, by
        rw [hmul]; exact hgβ⟩)
  rw [hidx]
  congr 1
  rw [Set.eq_univ_of_forall (s := cosetFixedSet H 1) fun ω => by
      change CFSG.ShultStronglyClosedTI.pointRightCosetMul H ω 1 = ω
      rw [hmul, rightCosetTranslate_one], Nat.card_univ]

theorem suzuki_degree_identity {q : ℕ} (hq : 1 ≤ q) :
    (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) = q ^ 3 * (q ^ 2 - q + 1) + 1 := by
  have h2 : q ≤ q ^ 2 := by nlinarith
  zify [hq, h2]
  ring

theorem pair_stabilizer_relIndex_eq_of_exclusion
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
    Nat.card (rightCosetSpace H) = (q ^ 2 + 1) * (q ^ 2 * (q - 1) + 1) ∧
      (pairPointStabilizer H beta).relIndex H = q ^ 3 * (q ^ 2 - q + 1) := by
  intro q
  obtain ⟨m, k, _, _, hk, hm, hQ, -, ψ, -, -, hdeg, -⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨u, huB, hu⟩ := hBinv
  obtain ⟨-, hfix, -⟩ := proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1
    hbeta ht hproper hexcl huB hu
  obtain ⟨i, hi, hfixi, hΩ⟩ := hexcl u huB hu
  have hq4 : 4 ≤ q := by
    obtain ⟨-, hQ4, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht
      hproper
    exact hQ4
  have hi2 : i = 2 := by
    have hfix2 : Nat.card (rightFixedSet H u) = q ^ 2 + 1 := by rw [hfix]; exact hdeg
    have hqi : q ^ i = q ^ 2 := Nat.add_right_cancel (hfixi.symm.trans hfix2)
    exact Nat.pow_right_injective (by omega) hqi
  subst hi2
  have htwo := CyclicSemiregular.proper_pair_two_transitive h hcomm hsmallerR1 hbeta ht hproper
  refine ⟨hΩ, ?_⟩
  rw [pair_stabilizer_relIndex_eq_card_sub_one H hbeta htwo, hΩ, suzuki_degree_identity (by omega)]
  rfl

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
