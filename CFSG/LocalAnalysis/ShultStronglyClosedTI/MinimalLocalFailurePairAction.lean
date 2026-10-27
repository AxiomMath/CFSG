module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionTransitivity
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionConsequences

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailurePairAction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    let B := pairPointStabilizer H beta
    let E := triplePointStabilizer H z beta
    let J := (oddCore B).map B.subtype
    let R := rightInvolutionCommutatorSubgroup t J
    let K := Subgroup.closure (({z, t} : Set G) ∪ (R : Set G))
    let Q := Subgroup.closure (conjugacyWithin H z)
    let W := Subgroup.closure {c : G | ∃ a ∈ conjugacyWithin H z,
      ∃ b ∈ conjugacyWithin H z, a⁻¹ * b⁻¹ * a * b = c}
    K < ⊤ → W ≤ J →
      (∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
        ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
      W = ⊥ ∧ IsElemAbelian 2 Q ∧ E = B ⊓ Subgroup.centralizer ({z} : Set G) := by
  change minimalLocalFailureProperPairHull H z beta t < ⊤ →
    minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta →
    (∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
    minimalLocalFailureProperPairClassCommutators H z = ⊥ ∧
    IsElemAbelian 2 (minimalLocalFailurePairActionPointHull H z) ∧
    triplePointStabilizer H z beta =
      pairPointStabilizer H beta ⊓ Subgroup.centralizer ({z} : Set G)
  intro hproper hWJ
  have hdoubly := minimalLocalFailurePairAction_doubly_transitive h hbeta ht hWJ
  have hW := minimalLocalFailurePairAction_classCommutators_eq_bot_of_doubly_transitive
    h hbeta hdoubly hWJ
  have hQ := minimalLocalFailurePairActionPointHull_elementary_of_commutators_bot
    H h.local_datum.distinguished_order hW
  exact ⟨hdoubly, hW, hQ,
    minimalLocalFailurePairAction_triple_eq_pair_centralizer h hbeta ht hproper hQ⟩

end CFSG.ShultStronglyClosedTI
