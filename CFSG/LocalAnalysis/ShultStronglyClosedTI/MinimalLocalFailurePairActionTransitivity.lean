module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionAlgebra
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersectionCorrector

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection

universe u

variable {G : Type u} [Group G] [Finite G]

theorem minimalLocalFailurePairAction_eq_of_all_sylows
    (B E : Subgroup G) (hEB : E ≤ B)
    (hcontains : ∀ p : ℕ, p.Prime →
      ∃ P : Sylow p B, (P : Subgroup B).map B.subtype ≤ E) : E = B := by
  have hnot : ∀ p : ℕ, p.Prime → ¬ p ∣ E.relIndex B := by
    intro p hp
    obtain ⟨P, hP⟩ := hcontains p hp
    exact sylow_overgroup_relIndex_prime_to p hp B E P hP
  have hidx : E.relIndex B = 1 := by
    by_contra hne
    obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd hne
    exact hnot p hp hdiv
  exact le_antisymm hEB (Subgroup.relIndex_eq_one.mp hidx)

theorem minimalLocalFailurePairAction_odd_pair_sylow_in_triple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hWJ : minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta)
    (hnot : ¬ ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    ∃ P : Sylow p (pairPointStabilizer H beta),
      (P : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≤
        triplePointStabilizer H z beta := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let B := pairPointStabilizer H beta
  let W := minimalLocalFailureProperPairClassCommutators H z
  let P₀ : Sylow p B := Classical.choice inferInstance
  let P₀G := (P₀ : Subgroup B).map B.subtype
  have hP₀B : P₀G ≤ B := Subgroup.map_subtype_le _
  have hP₀H : P₀G ≤ H := hP₀B.trans (pairPointStabilizer_le_point H beta)
  have hP₀p : IsPGroup p P₀G := P₀.isPGroup'.map B.subtype
  have hfixed : 2 ≤ Nat.card (pointFixedSet H P₀G) :=
    two_le_pointFixedSet_card_of_pair H P₀G (rightCosetMk H 1) beta (Ne.symm hbeta)
      ((mem_pointFixedSet_iff H P₀G _).mpr (hP₀B.trans inf_le_left))
      ((mem_pointFixedSet_iff H P₀G _).mpr (hP₀B.trans inf_le_right))
  let property : Subgroup G → Prop := fun A =>
    A ≤ H ∧ IsPGroup p A ∧ 2 ≤ Nat.card (pointFixedSet H A)
  obtain ⟨A, hP₀A, hmax⟩ := Finite.exists_le_maximal
    (show property P₀G from ⟨hP₀H, hP₀p, hfixed⟩)
  have hlocalmax : ∀ X : Subgroup G, X ≤ H → IsPGroup p X → A ≤ X →
      2 ≤ Nat.card (pointFixedSet H X) → X = A := by
    intro X hXH hXp hAX hXfixed
    exact le_antisymm (hmax.2 ⟨hXH, hXp, hXfixed⟩ hAX) hAX
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hdichotomy := local_involution_point_maximal_prime_fixed_set_dichotomy
    H z h.local_datum S hzS hzcenter p hp hpodd A
    hmax.1.2.1 hmax.1.1 hmax.1.2.2 hlocalmax
  obtain ⟨u, huclass, huA, huH⟩ :
      ∃ u ∈ involutionPointClass z, u ∈ Subgroup.normalizer (A : Set G) ∧ u ∈ H := by
    rcases hdichotomy.2.2.2.1 with hdouble | hlarge
    · exact False.elim (hnot (by
        simpa only [pointRightCosetMul_eq_translate] using hdouble.2))
    · exact hlarge.2
  have huHclass : u ∈ conjugacyWithin H z := by
    obtain ⟨a, ha⟩ := huclass
    change a⁻¹ * z * a = u at ha
    have haH : a ∈ H := (pointClass_conjugate_mem_iff h.local_datum a).mp
      (by change a⁻¹ * z * a ∈ H; rw [ha]; exact huH)
    exact ⟨⟨a, haH⟩, ha⟩
  rw [point_class_eq_pair_stabilizer_class h.local_datum S hzS hzcenter hbeta ht] at huHclass
  obtain ⟨b, hb⟩ := huHclass
  let n : G := (b : G)⁻¹
  let A₁ := rightConjugate A n
  let P₁ := rightConjugate P₀G n
  have hnH : n ∈ H := (pairPointStabilizer_le_point H beta) (B.inv_mem b.property)
  have hA₁H : A₁ ≤ H := by
    rintro a ⟨x, hx, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      H.mul_mem (H.mul_mem (H.inv_mem hnH) (hmax.1.1 hx)) hnH
  have hA₁p : IsPGroup p A₁ := hmax.1.2.1.map (MulAut.conj n⁻¹).toMonoidHom
  have hP₁A₁ : P₁ ≤ A₁ := Subgroup.map_mono hP₀A
  have hP₁B : P₁ ≤ B := by
    rintro a ⟨x, hx, rfl⟩
    simpa only [n, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      B.mul_mem (B.mul_mem b.property (hP₀B hx)) (B.inv_mem b.property)
  have hun : rightConjugateElem u n = z := by
    dsimp only [n, rightConjugateElem]
    rw [← hb]
    simp only [inv_inv]
    group
  have hzA₁ : z ∈ Subgroup.normalizer (A₁ : Set G) := by
    rw [← hun]
    exact right_conjugate_mem_normalizer huA n
  have hWH : W ≤ H := minimalLocalFailureProperPairClassCommutators_le_point H
    h.local_datum.distinguished_mem
  have hzW : z ∈ Subgroup.normalizer (W : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mp
      (minimalLocalFailureProperPairClassCommutators_normal_in_point H
        h.local_datum.distinguished_mem) h.local_datum.distinguished_mem
  have hcommP : ∀ a ∈ P₁, z⁻¹ * a⁻¹ * z * a ∈ W := by
    intro a ha
    exact minimalLocalFailurePairAction_odd_prime_commutator_mem H
      h.local_datum.distinguished_mem h.local_datum.distinguished_order
      p hpodd A₁ hA₁H hA₁p hzA₁ (hP₁A₁ ha)
  have hjoinB : P₁ ⊔ W ≤ B := sup_le hP₁B (hWJ.trans (Subgroup.map_subtype_le _))
  have hjoinnorm : z ∈ Subgroup.normalizer ((P₁ ⊔ W : Subgroup G) : Set G) :=
    minimalLocalFailurePairAction_join_normalized_of_commutators P₁ W z
      h.local_datum.distinguished_order hzW hcommP
  have hP₁E : P₁ ≤ triplePointStabilizer H z beta :=
    le_sup_left.trans (invariant_pair_subgroup_le_triple hjoinB hjoinnorm)
  have hP₁card : Nat.card P₁ = p ^ (Nat.card B).factorization p := by
    change Nat.card (P₀G.map (MulAut.conj n⁻¹).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective,
      Subgroup.card_map_of_injective B.subtype_injective, P₀.card_eq_multiplicity]
  obtain ⟨P, hP⟩ := p_subgroup_sylow_of_full_card p hp B P₁ hP₁B hP₁card
  exact ⟨P, hP.symm ▸ hP₁E⟩

theorem minimalLocalFailurePairAction_two_pair_sylow_in_triple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1) :
    ∃ P : Sylow 2 (pairPointStabilizer H beta),
      (P : Subgroup (pairPointStabilizer H beta)).map (pairPointStabilizer H beta).subtype ≤
        triplePointStabilizer H z beta := by
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hmOdd := point_subgroup_full_class_card_odd h.local_datum S hzS hzcenter
  have hm₂ : 2 ^ (Nat.card (conjugacyWithin H z)).factorization 2 = 1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd hmOdd.not_two_dvd_nat, pow_zero]
  apply ((local_involution_point_three_point_sylow_criterion
    h.local_datum S hzS hzcenter beta hbeta).2 2 Nat.prime_two).2.1.mpr
  refine ⟨⊥, bot_le, ?_, ?_, ?_⟩
  · exact isPGroup_iff_pow_pow_eq_one.mpr fun a => ⟨0, by
      have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp a.property)
      simp only [ha, one_pow]⟩
  · apply Subgroup.mem_normalizer_iff.mpr
    intro x
    simp only [Subgroup.mem_bot]
    constructor
    · intro hx
      rw [hx, mul_one, mul_inv_cancel]
    · intro hx
      have hh := congrArg (fun a : G => z⁻¹ * a * z) hx
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul] using hh
  · have hclassbot : conjugacyWithin (⊥ : Subgroup G) z = {z} := by
      ext a
      constructor
      · rintro ⟨g, rfl⟩
        have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
        simp only [hg, inv_one, one_mul, mul_one, Set.mem_singleton_iff]
      · intro ha
        rw [Set.mem_singleton_iff] at ha
        subst a
        exact ⟨1, by simp⟩
    rw [hm₂, hclassbot, Nat.card_unique]

theorem minimalLocalFailurePairAction_doubly_transitive
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hWJ : minimalLocalFailureProperPairClassCommutators H z ≤ pairOddCore H beta) :
    ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d := by
  by_contra hnot
  apply minimalLocalFailurePairAction_triple_ne_pair h hbeta ht hWJ
  apply minimalLocalFailurePairAction_eq_of_all_sylows
    (pairPointStabilizer H beta) (triplePointStabilizer H z beta) inf_le_left
  intro p hp
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · exact minimalLocalFailurePairAction_two_pair_sylow_in_triple h hbeta
  · exact minimalLocalFailurePairAction_odd_pair_sylow_in_triple h hbeta ht hWJ hnot p hp hpodd

end CFSG.ShultStronglyClosedTI
