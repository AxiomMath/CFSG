module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairCommutators

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimal_local_embedding_proper_pair_commutator_reduction
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    let B := pairPointStabilizer H beta
    let J := (oddCore B).map B.subtype
    let R := Subgroup.closure (Set.range (fun j : J => t⁻¹ * (j : G)⁻¹ * t * j))
    let K := Subgroup.closure (({z, t} : Set G) ∪ (R : Set G))
    let M := H.subgroupOf K
    let N := oddCore K
    let W := Subgroup.closure {c : G | ∃ a ∈ conjugacyWithin H z,
      ∃ b ∈ conjugacyWithin H z, a⁻¹ * b⁻¹ * a * b = c}
    K < ⊤ →
      fusionStronglyEmbedded M ∧
      (∃ s ∈ conjugacyWithin H z, s ≠ z ∧ Commute z s ∧
        IsElemAbelian 2 (Subgroup.closure ({z, s} : Set G)) ∧
        Nat.card (Subgroup.closure ({z, s} : Set G)) = 4 ∧
        Subgroup.closure ({z, s} : Set G) ≤ H ⊓ K) ∧
      conjugacyWithin H z ⊆ (H ⊓ K : Set G) ∧
      N.map K.subtype ≤ B ∧
      ((∀ a b : K, a ∈ M → orderOf a = 2 → b ∈ M → orderOf b = 2 →
        Commute (QuotientGroup.mk a : K ⧸ N) (QuotientGroup.mk b : K ⧸ N)) →
        (W.subgroupOf H).Normal ∧ W ≤ J) := by
  change minimalLocalFailureProperPairHull H z beta t < ⊤ →
    fusionStronglyEmbedded (H.subgroupOf (minimalLocalFailureProperPairHull H z beta t)) ∧
    (∃ s ∈ conjugacyWithin H z, s ≠ z ∧ Commute z s ∧
      IsElemAbelian 2 (Subgroup.closure ({z, s} : Set G)) ∧
      Nat.card (Subgroup.closure ({z, s} : Set G)) = 4 ∧
      Subgroup.closure ({z, s} : Set G) ≤ H ⊓ minimalLocalFailureProperPairHull H z beta t) ∧
    conjugacyWithin H z ⊆ (H ⊓ minimalLocalFailureProperPairHull H z beta t : Set G) ∧
    minimalLocalFailureProperPairOddCore H z beta t ≤ pairPointStabilizer H beta ∧
    _
  intro hproper
  refine ⟨minimalLocalFailureProperPair_stronglyEmbedded h hbeta ht hproper,
    minimalLocalFailureProperPair_four_group h hbeta ht,
    minimalLocalFailureProperPair_class_subset h.local_datum h.central_sylow hbeta ht,
    minimalLocalFailureProperPairOddCore_le_pair_stabilizer h hbeta ht hproper, ?_⟩
  intro hcomm
  exact minimalLocalFailureProperPairClassCommutators_normal_and_le_pair_oddCore
    h hbeta ht hproper hcomm

end CFSG.ShultStronglyClosedTI
