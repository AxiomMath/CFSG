module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFullCyclicFixed
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFlip
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerNormalizer

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pair_inf_iff (H : Subgroup G) (beta : rightCosetSpace H) (C : Subgroup G) (g : G) :
    g ∈ pairPointStabilizer H beta ⊓ C ↔
      g ∈ C ∧ rightCosetTranslate H (rightCosetMk H 1) g = rightCosetMk H 1 ∧
        rightCosetTranslate H beta g = beta := by
  rw [Subgroup.mem_inf, pairPointStabilizer, Subgroup.mem_inf, mem_rightCosetStabilizer_iff,
    mem_rightCosetStabilizer_iff]
  tauto

omit [Finite G] in
theorem pointFixedSet_eq_translate (H P : Subgroup G) :
    pointFixedSet H P = {omega | ∀ g ∈ P, rightCosetTranslate H omega g = omega} := by
  ext omega
  simp only [pointFixedSet, Set.mem_ofPred_eq, pointRightCosetMul_eq_translate]

theorem odd_card_pointClass_of_proper_pair
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Odd (Nat.card (conjugacyWithin H z)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hXodd, hXm, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  rwa [← hXm]

theorem prime_centralizer_scalar_case
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {p : ℕ} (hp : p.Prime) (hpm : p ∣ Nat.card (conjugacyWithin H z))
    {y : G} (hyB : y ∈ pairPointStabilizer H beta)
    (hyX : rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
      Subgroup.centralizer ({y} : Set G))
    (P : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) :
      Subgroup G)) :
    let B := pairPointStabilizer H beta
    let C := Subgroup.centralizer ({y} : Set G)
    pointFixedSet H ((P : Subgroup (B ⊓ C : Subgroup G)).map (B ⊓ C).subtype) =
        {rightCosetMk H 1, beta} ∧
      ∃ S : Sylow p C, (S : Subgroup C).map C.subtype =
        (P : Subgroup (B ⊓ C : Subgroup G)).map (B ⊓ C).subtype := by
  intro B C
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let Q := minimalLocalFailurePairActionPointHull H z
  obtain ⟨hQ, -, hQclass, hQH, hQnorm, hXB, hXnormal, hXcyclic, -, hXm, -, hinv, -, hclassB,
    -⟩ := proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
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
  have hswap : rightCosetTranslate H (rightCosetMk H 1) t = beta ∧
      rightCosetTranslate H beta t = rightCosetMk H 1 :=
    ⟨ht.2, rightPairFlipFiber_swap h.local_datum.distinguished_order ht⟩
  have hclass : conjugacyWithin B t = ({t} : Set G) * (X : Set G) := by
    rw [Set.singleton_mul]
    exact hclassB
  let : Fact p.Prime := ⟨hp⟩
  let A : Sylow p X := default
  obtain ⟨-, -, -, -, -, hR⟩ :=
    CFSG.ProperTwoGeneratedCore.local_involution_point_full_cyclic_sylow_fixed_points H Q X z
      h.local_datum S₂ hzS hzcenter hQH hQnormal (isPGroup_two_of_isElemAbelian hQ) hzQ beta
      hbeta t ht.1 hswap hXB hXnormal hXcyclic hXm hinv hclass p hp hpm A
  have hyCX : y ∈ B ⊓ Subgroup.centralizer (X : Set G) := by
    refine ⟨hyB, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hyX hx)
  have hfix := (hR y hyCX P).2
  refine ⟨hfix, ?_⟩
  have hodd := odd_card_pointClass_of_proper_pair h hcomm hsmallerR1 hbeta ht hproper
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm)
  refine exists_sylow_of_fixed_pair (fun omega g => rightCosetTranslate H omega g)
    (rightCosetTranslate_one H) (rightCosetTranslate_mul H) hp2 hbeta.symm C (B ⊓ C)
    (fun g => by rw [mem_pair_inf_iff]) P ?_
  rw [← pointFixedSet_eq_translate]
  exact hfix

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
