module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerField

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

theorem proper_pair_two_transitive {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
  let Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨hQ, hQ4, hQclass, hQH, hQnorm, -, -, -, -, hXm, hXQ, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨S₂, hzS, hzcenter⟩ := h.central_sylow
  have hQnormal : (Q.subgroupOf H).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hmem := hQnorm ((g : G))⁻¹ (H.inv_mem g.2) _ hn
    simpa only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  have hzQ : z ∈ Q := by
    have hz : z ∈ conjugacyWithin H z := ⟨1, by simp⟩
    rw [← hQclass] at hz
    exact hz.1
  obtain ⟨-, -, htwo⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_normal_two_hull_sylow_fixed_points
      h.local_datum S₂ hzS hzcenter hQH hQnormal (isPGroup_two_of_isElemAbelian hQ) hzQ
  have hm1 : 1 < Nat.card (conjugacyWithin H z) := by
    rw [← hXm, hXQ]
    omega
  intro a b c d hab hcd
  obtain ⟨g, h1, h2⟩ := htwo hm1 a b c d hab hcd
  rw [pointRightCosetMul_eq_translate] at h1 h2
  exact ⟨g, h1, h2⟩

theorem minimalLocalFailure_prime_centralizer_sylow_fixed_points
    {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let alpha := rightCosetMk H 1
    let B := pairPointStabilizer H beta
    let m := Nat.card (conjugacyWithin H z)
    (∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
        ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d) ∧
      ∀ p : ℕ, p.Prime → p ∣ m → ∀ y ∈ B, orderOf y = p →
        ∀ P : Sylow p (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
          (∃ S : Sylow p (Subgroup.centralizer ({y} : Set G)),
            (S : Subgroup (Subgroup.centralizer ({y} : Set G))).map
                (Subgroup.centralizer ({y} : Set G)).subtype =
              (P : Subgroup (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
                (B ⊓ Subgroup.centralizer ({y} : Set G)).subtype) ∧
          pointFixedSet H
              ((P : Subgroup (B ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)).map
                (B ⊓ Subgroup.centralizer ({y} : Set G)).subtype) = {alpha, beta} := by
  intro alpha B m
  have hdt := proper_pair_two_transitive h hcomm hsmallerR1 hbeta ht hproper
  refine ⟨hdt, fun p hp hpm y hyB hy P => ?_⟩
  by_cases hXy : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
      Subgroup.centralizer ({y} : Set G)
  · obtain ⟨hfix, hS⟩ :=
      prime_centralizer_scalar_case h hcomm hsmallerR1 hbeta ht hproper hp hpm hyB hXy P
    exact ⟨hS, hfix⟩
  · obtain ⟨hQ, -, -, -, -, -, -, -, -, hXm, hXQ, -⟩ :=
      proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
    obtain ⟨e, he⟩ := (isPGroup_two_of_isElemAbelian hQ).exists_card_eq
    have hpq : p ∣ 2 ^ e - 1 := by
      rw [← he, ← hXQ, hXm]
      exact hpm
    obtain ⟨hfix, hS⟩ := prime_centralizer_field_case h hcomm hsmallerR1 hbeta ht hproper he hp
      hpq hdt hyB hy hXy P
    exact ⟨hS, hfix⟩

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
