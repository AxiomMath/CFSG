module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregularPrime
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregularPairs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedOddFixedSet

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

variable {G : Type} [Group G] [Finite G]

theorem proper_pair_torus_prime_fixed_set
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {x : G} (hxX : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta))
    {p : ℕ} (hp : p.Prime) (hx : orderOf x = p) :
    {omega : rightCosetSpace H | rightCosetTranslate H omega x = omega} =
      {rightCosetMk H 1, beta} := by
  obtain ⟨-, -, -, -, -, hXB, -, -, hXodd, hXm, -, hinv, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  let A := Subgroup.zpowers x
  let Δ := pointFixedSet H A
  have hpX : p ∣ Nat.card (rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) :=
    hx ▸ Subgroup.orderOf_dvd_natCard _ hxX
  have hpm : p ∣ Nat.card (conjugacyWithin H z) := hXm ▸ hpX
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr hpX)
  have htorder : orderOf t = 2 :=
    order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  have htt : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two htorder
  have hAab : A ≤ rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta :=
    (Subgroup.zpowers_le).mpr (hXB hxX)
  have hAodd : Odd (Nat.card A) := by
    rw [Nat.card_zpowers, hx]
    exact hp.odd_of_ne_two hp2
  have htA : t ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_zpowers_of_inv htt (hinv x hxX)
  have hAt : ⁅A, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro h0
    have hxt : x ∈ Subgroup.centralizer ({t} : Set G) :=
      (commutator_zpowers_eq_bot_iff A t).mp h0 (Subgroup.mem_zpowers x)
    have hxx : x⁻¹ = x := by
      have hconj := hinv x hxX
      change t⁻¹ * x * t = x⁻¹ at hconj
      rw [← hconj, mul_assoc, Subgroup.mem_centralizer_singleton_iff.mp hxt,
        inv_mul_cancel_left]
    have hx2 : x ^ 2 = 1 := by
      rw [sq]
      nth_rw 1 [← hxx]
      exact inv_mul_cancel x
    have hdvd : p ∣ 2 := hx ▸ orderOf_dvd_of_pow_eq_one hx2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  obtain ⟨gamma, hgamma⟩ := class_fixed_exists h.local_datum ht.1
  have hgamma' : pointRightCosetMul H gamma t = gamma := by
    rw [pointRightCosetMul_eq_translate]
    exact hgamma
  have htab : pointRightCosetMul H (rightCosetMk H 1) t = beta := by
    rw [pointRightCosetMul_eq_translate]
    exact ht.2
  obtain ⟨-, -, -, heven, -, -, -, -, -, hnot⟩ :=
    minimalLocalFailure_inverted_odd_subgroup_fixed_set_obstruction h hcomm hsmallerR1
      hbeta.symm ht.1 htab hAab hAodd htA hAt hgamma'
  have hpres : ∀ ω ∈ Δ, ∀ c ∈ Subgroup.centralizer (A : Set G), pointRightCosetMul H ω c ∈ Δ :=
    fun ω hω c hc => normalizer_preserves_pointFixedSet
      (Subgroup.centralizer_le_normalizer (A : Set G) hc) hω
  have hle : Nat.card Δ ≤ 2 := by
    by_contra hgt
    push Not at hgt
    exact hnot hgt (two_transitive_of_unordered_pair_transitive (pointRightCosetMul H)
      (pointRightCosetMul_one H) (pointRightCosetMul_mul H) (Subgroup.centralizer (A : Set G)) Δ
      (Set.toFinite Δ) hpres heven hgt
      (centralizer_unordered_pair_transitive h hcomm hsmallerR1 hbeta ht hproper hp hpm hx))
  have hα : rightCosetMk H 1 ∈ Δ := (mem_pointFixedSet_iff H A _).mpr (hAab.trans inf_le_left)
  have hβ : beta ∈ Δ := (mem_pointFixedSet_iff H A beta).mpr (hAab.trans inf_le_right)
  have hsub : ({rightCosetMk H 1, beta} : Set (rightCosetSpace H)) ⊆ Δ := by
    intro ω hω
    rcases hω with rfl | hω
    · exact hα
    · rw [Set.mem_singleton_iff] at hω
      rw [hω]
      exact hβ
  have hpair : ({rightCosetMk H 1, beta} : Set (rightCosetSpace H)).ncard = 2 :=
    Set.ncard_pair hbeta.symm
  rw [fixed_set_eq_pointFixedSet_zpowers]
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [hpair, ← Nat.card_coe_set_eq]
  exact hle

theorem minimalLocalFailure_proper_pair_cyclic_semiregularity
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let alpha := rightCosetMk H 1
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let m := Nat.card (conjugacyWithin H z)
    IsCyclic X ∧ Odd (Nat.card X) ∧ Nat.card X = m ∧
      (∀ x ∈ X, ∀ omega : rightCosetSpace H, omega ≠ alpha → omega ≠ beta →
        rightCosetTranslate H omega x ≠ alpha ∧ rightCosetTranslate H omega x ≠ beta) ∧
      (∀ x ∈ X, ∀ omega : rightCosetSpace H, omega ≠ alpha → omega ≠ beta →
        rightCosetTranslate H omega x = omega → x = 1) ∧
      (∀ x ∈ X, x ≠ 1 →
        {omega : rightCosetSpace H | rightCosetTranslate H omega x = omega} = {alpha, beta}) ∧
      m ∣ Nat.card (rightCosetSpace H) - 2 := by
  intro alpha X m
  obtain ⟨-, -, -, -, -, hXB, -, hcyc, hodd, hXm, -⟩ :=
    proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  have hfixX : ∀ x ∈ X, x ≠ 1 →
      {omega : rightCosetSpace H | rightCosetTranslate H omega x = omega} = {alpha, beta} := by
    intro x hx hx1
    have hd : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
    have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    have hw : orderOf (x ^ (orderOf x / q)) = q := orderOf_pow_orderOf_div hx0 hqd
    have hwfix := proper_pair_torus_prime_fixed_set h hcomm hsmallerR1 hbeta ht hproper
      (X.pow_mem hx _) hq hw
    apply Set.Subset.antisymm
    · intro ω hω
      rw [← hwfix]
      have hxst : x ∈ rightCosetStabilizer H ω := (mem_rightCosetStabilizer_iff H ω x).mpr hω
      exact (mem_rightCosetStabilizer_iff H ω _).mp
        ((rightCosetStabilizer H ω).pow_mem hxst _)
    · intro ω hω
      have hxB := hXB hx
      rcases hω with rfl | hω
      · exact (mem_rightCosetStabilizer_iff H _ x).mp hxB.1
      · rw [Set.mem_singleton_iff] at hω
        rw [hω]
        exact (mem_rightCosetStabilizer_iff H beta x).mp hxB.2
  have hsemi : ∀ x ∈ X, ∀ omega : rightCosetSpace H, omega ≠ alpha → omega ≠ beta →
      rightCosetTranslate H omega x = omega → x = 1 := by
    intro x hx omega hα hβ hfix
    by_contra hx1
    have hmem : omega ∈ {omega : rightCosetSpace H | rightCosetTranslate H omega x = omega} :=
      hfix
    rw [hfixX x hx hx1] at hmem
    rcases hmem with h1 | h1
    · exact hα h1
    · exact hβ h1
  let Γ : Set (rightCosetSpace H) := {alpha, beta}ᶜ
  have hpres : ∀ ω ∈ Γ, ∀ x ∈ X, rightCosetTranslate H ω x ∈ Γ := by
    intro ω hω x hx hmem
    apply hω
    have hxinv := hXB (X.inv_mem hx)
    have hback : rightCosetTranslate H (rightCosetTranslate H ω x) x⁻¹ = ω := by
      rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
    rcases hmem with h1 | h1
    · left
      rw [← hback, h1]
      exact (mem_rightCosetStabilizer_iff H _ _).mp hxinv.1
    · right
      rw [Set.mem_singleton_iff] at h1 ⊢
      rw [← hback, h1]
      exact (mem_rightCosetStabilizer_iff H _ _).mp hxinv.2
  refine ⟨hcyc, hodd, hXm, fun x hx omega hα hβ => ?_, hsemi, hfixX, ?_⟩
  · have hmem := hpres omega (by rintro (h1 | h1); exacts [hα h1, hβ h1]) x hx
    exact ⟨fun h1 => hmem (Or.inl h1), fun h1 => hmem (Or.inr h1)⟩
  have hfree : ∀ ω ∈ Γ, ∀ x ∈ X, rightCosetTranslate H ω x = ω → x = 1 := by
    intro ω hω x hx hfix
    exact hsemi x hx ω (fun h1 => hω (Or.inl h1)) (fun h1 => hω (Or.inr h1)) hfix
  have hdvd := card_dvd_card_of_free (fun ω g => rightCosetTranslate H ω g)
    (rightCosetTranslate_one H) (rightCosetTranslate_mul H) X Γ (Set.toFinite Γ) hpres hfree
  have hΓ : Nat.card Γ = Nat.card (rightCosetSpace H) - 2 := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl, Set.ncard_pair hbeta.symm]
  change Nat.card (conjugacyWithin H z) ∣ Nat.card (rightCosetSpace H) - 2
  rw [← hXm, ← hΓ]
  exact hdvd

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
