module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicCommutator
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicProducts

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem proper_pair_cyclic_commutator
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let I := pairOddCore H beta
    let X := rightInvolutionCommutatorSubgroup t I
    let K := minimalLocalFailureProperPairHull H z beta t
    let M := H ⊓ K
    let R := (CFSG.oddCore K).map K.subtype
    let Q := minimalLocalFailurePairActionPointHull H z
    let m := Nat.card (conjugacyWithin H z)
    IsElemAbelian 2 Q ∧ 4 ≤ Nat.card Q ∧
      (Q : Set G) \ {1} = conjugacyWithin H z ∧
      conjugacyWithin H z = conjugacyWithin M z ∧
      conjugacyWithin M z = {x : G | x ∈ M ∧ orderOf x = 2} ∧
      CFSG.oddCore K ≤ Subgroup.center K ∧ R ≤ Subgroup.centralizer (K : Set G) ∧
      I ≤ B ∧ X ≤ I ∧ X ≤ K ∧ IsCyclic X ∧ Odd (Nat.card X) ∧ Nat.card X = m ∧
      X ⊓ R = ⊥ ∧
      (X : Set G) = {x : G | x ∈ I ∧ rightConjugateElem x t = x⁻¹} ∧
      (∀ x : G, x ∈ X → rightConjugateElem x t = x⁻¹) ∧
      (∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
        Even (orderOf (r * s)) → Commute r s) ∧
      (∀ r s : G, r ∈ involutionPointClass z → s ∈ involutionPointClass z →
        r ≠ s → Commute r s → r * s ∈ involutionPointClass z) := by
  obtain ⟨_, _, _, hQ, _, hcardQ, _⟩ := proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨hQclass, hclasses, hInv⟩ := proper_pair_point_root_classes h hcomm hbeta ht hproper
  obtain ⟨hcentral, hcentralAmbient⟩ := proper_pair_full_odd_core_central h hcomm hbeta ht hproper
  obtain ⟨hXI, hXK, hcyclic, hodd⟩ :=
    proper_pair_commutator_cyclic_and_odd h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨_, hinv, hset⟩ :=
    proper_pair_commutator_exact_inversion_set h hcomm hsmallerR1 hbeta ht hproper
  exact ⟨hQ, hcardQ, hQclass, hclasses, hInv, hcentral, hcentralAmbient,
    (pairOddCore_le H beta t).1, hXI, hXK, hcyclic, hodd,
    proper_pair_commutator_card h hcomm hsmallerR1 hbeta ht hproper,
    proper_pair_commutator_inf_odd_core_eq_bot h hcomm hsmallerR1 hbeta ht hproper,
    hset, hinv,
    fun _ _ hr hs heven => proper_pair_even_class_product_commutes
      h hcomm hbeta ht hproper hr hs heven,
    fun _ _ hr hs hne hrs => proper_pair_distinct_commuting_class_product_mem
      h hcomm hbeta ht hproper hr hs hne hrs⟩

end CFSG.ShultStronglyClosedTI.CyclicPair
