module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersectionCorrector
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionNormalizedIntersection

universe u

variable {G : Type u} [Group G]

theorem pairSylow_maximal_two_point_rightConjugate
    (H P : Subgroup G) (p : ℕ) (n : G)
    (hmax : IsMaximalTwoPointPrime H p P) :
    IsMaximalTwoPointPrime H p (rightConjugate P n) := by
  intro Q hQ hPQ hfixed
  have hQback : IsPGroup p (rightConjugate Q n⁻¹) :=
    hQ.map (MulAut.conj (n⁻¹)⁻¹).toMonoidHom
  have hPback : P ≤ rightConjugate Q n⁻¹ := by
    intro x hx
    have hxn : n⁻¹ * x * n ∈ rightConjugate P n := by
      apply (mem_right_conjugate_iff P n _).mpr
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hx
    apply (mem_right_conjugate_iff Q n⁻¹ x).mpr
    simpa only [inv_inv] using hPQ hxn
  have hbackfixed : 2 ≤ Nat.card (pointFixedSet H (rightConjugate Q n⁻¹)) := by
    rwa [pointFixedSet_rightConjugate_card]
  have hback := hmax _ hQback hPback hbackfixed
  apply le_antisymm _ hPQ
  intro x hx
  have hxback : n * x * n⁻¹ ∈ rightConjugate Q n⁻¹ := by
    apply (mem_right_conjugate_iff Q n⁻¹ _).mpr
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hx
  rw [hback] at hxback
  exact (mem_right_conjugate_iff P n x).mpr hxback

variable [Finite G]

theorem pairSylow_bad_sylow_large_invariant_maximal
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hbad : ∃ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) ≠ 2) :
    ∃ P : Subgroup G, IsPGroup p P ∧ P ≤ H ∧
      z ∈ Subgroup.normalizer (P : Set G) ∧
      3 ≤ Nat.card (pointFixedSet H P) ∧ IsMaximalTwoPointPrime H p P := by
  have hnot : ¬ (⊤ : Subgroup G) ≤ H := fun htop =>
    h.local_datum.proper (top_le_iff.mp htop)
  obtain ⟨x, _, hxH⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  let beta := rightCosetMk H x
  have hbeta : beta ≠ rightCosetMk H 1 := by
    intro heq
    apply hxH
    apply (point_right_base_fixed_iff H x).mp
    simpa only [pointRightCosetMul_eq_translate, rightCosetTranslate_mk, one_mul] using heq
  have hbotfixed : 2 ≤ Nat.card (pointFixedSet H (⊥ : Subgroup G)) :=
    two_le_pointFixedSet_card_of_pair H ⊥ (rightCosetMk H 1) beta (Ne.symm hbeta)
      ((mem_pointFixedSet_iff H ⊥ _).mpr bot_le)
      ((mem_pointFixedSet_iff H ⊥ _).mpr bot_le)
  have hbotp : IsPGroup p (⊥ : Subgroup G) := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro a
    have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.mp a.property)
    exact ⟨0, by simp only [ha, one_pow]⟩
  let property : Subgroup G → Prop := fun A =>
    A ≤ H ∧ IsPGroup p A ∧ 2 ≤ Nat.card (pointFixedSet H A)
  obtain ⟨P₀, _, hmax⟩ := Finite.exists_le_maximal
    (show property ⊥ from ⟨bot_le, hbotp, hbotfixed⟩)
  have hlocalmax : IsLocallyMaximalTwoPointPrime H p P₀ := by
    intro Q hQH hQp hPQ hQfixed
    exact le_antisymm (hmax.2 ⟨hQH, hQp, hQfixed⟩ hPQ) hPQ
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hdichotomy := local_involution_point_maximal_prime_fixed_set_dichotomy
    H z h.local_datum S hzS hzcenter p hp hodd P₀
    hmax.1.2.1 hmax.1.1 hmax.1.2.2 hlocalmax
  have hglobal : IsMaximalTwoPointPrime H p P₀ := hdichotomy.2.2.1
  obtain ⟨hlarge, u, huclass, huP, huH⟩ :
      3 ≤ Nat.card (pointFixedSet H P₀) ∧
        ∃ u ∈ involutionPointClass z, u ∈ Subgroup.normalizer (P₀ : Set G) ∧ u ∈ H := by
    rcases hdichotomy.2.2.2.1 with htwo | hlarge
    · obtain ⟨R, hR⟩ := maximal_two_fixed_points_is_ambient_sylow
        H P₀ p hp hodd hmax.1.2.1 htwo.1 hglobal
      obtain ⟨Rbad, hRbad⟩ := hbad
      apply False.elim
      apply hRbad
      rw [ambient_sylow_pointFixedSet_card_eq H p hp R Rbad, hR]
      exact htwo.1
    · exact hlarge
  obtain ⟨a, ha⟩ := huclass
  change a⁻¹ * z * a = u at ha
  have haH : a ∈ H := (pointClass_conjugate_mem_iff h.local_datum a).mp
    (by change a⁻¹ * z * a ∈ H; rw [ha]; exact huH)
  let n := a⁻¹
  let P := rightConjugate P₀ n
  have hPH : P ≤ H := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [n, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      H.mul_mem (H.mul_mem haH (hmax.1.1 hx)) (H.inv_mem haH)
  have hun : rightConjugateElem u n = z := by
    dsimp only [n, rightConjugateElem]
    rw [← ha]
    simp only [inv_inv]
    group
  have hzP : z ∈ Subgroup.normalizer (P : Set G) := by
    rw [← hun]
    exact right_conjugate_mem_normalizer huP n
  refine ⟨P, hmax.1.2.1.map (MulAut.conj n⁻¹).toMonoidHom, hPH, hzP, ?_,
    pairSylow_maximal_two_point_rightConjugate H P₀ p n hglobal⟩
  simpa only [P, pointFixedSet_rightConjugate_card] using hlarge

theorem pairSylow_full_pair_family_of_maximal_invariant
    (H P : Subgroup G) (z : G) (p : ℕ) (hP : IsPGroup p P) (hPH : P ≤ H)
    (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (hfixed : 2 ≤ Nat.card (pointFixedSet H P))
    (hmax : IsMaximalTwoPointPrime H p P) :
    ∃ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 ∧
      ∃ Q : Sylow p (pairPointStabilizer H beta),
        (Q : Subgroup (pairPointStabilizer H beta)).map
          (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta := by
  have hcard : 1 < (pointFixedSet H P).ncard := by
    change 1 < Nat.card (pointFixedSet H P)
    omega
  obtain ⟨beta, hbetaP, hbeta⟩ := Set.exists_ne_of_one_lt_ncard hcard (rightCosetMk H 1)
  let B := pairPointStabilizer H beta
  have hPB : P ≤ B := le_inf (by simpa only [rightCosetStabilizer_base] using hPH)
    ((mem_pointFixedSet_iff H P beta).mp hbetaP)
  have hPi : IsPGroup p (P.subgroupOf B) := hP.of_injective
    (Subgroup.subgroupOfEquivOfLe hPB).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hPB).injective
  obtain ⟨Q, hPQ⟩ := hPi.exists_le_sylow
  let QG := (Q : Subgroup B).map B.subtype
  have hPQG : P ≤ QG := by
    have hmap := Subgroup.map_mono (f := B.subtype) hPQ
    rwa [Subgroup.map_subgroupOf_eq_of_le hPB] at hmap
  have hQtwo : 2 ≤ Nat.card (pointFixedSet H QG) :=
    two_le_pointFixedSet_card_of_pair H QG (rightCosetMk H 1) beta (Ne.symm hbeta)
      ((mem_pointFixedSet_iff H QG _).mpr ((Subgroup.map_subtype_le _).trans inf_le_left))
      ((mem_pointFixedSet_iff H QG _).mpr ((Subgroup.map_subtype_le _).trans inf_le_right))
  have hQeq : QG = P := hmax _ (Q.isPGroup'.map B.subtype) hPQG hQtwo
  refine ⟨beta, hbeta, Q, ?_⟩
  change QG ≤ triplePointStabilizer H z beta
  rw [hQeq]
  exact invariant_pair_subgroup_le_triple hPB hzP

theorem pairSylow_bad_sylow_full_pair_family
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hbad : ∃ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) ≠ 2) :
    ∃ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 ∧
      ∃ Q : Sylow p (pairPointStabilizer H beta),
        (Q : Subgroup (pairPointStabilizer H beta)).map
          (pairPointStabilizer H beta).subtype ≤ triplePointStabilizer H z beta := by
  obtain ⟨P, hP, hPH, hzP, hfixed, hmax⟩ :=
    pairSylow_bad_sylow_large_invariant_maximal h p hp hodd hbad
  exact pairSylow_full_pair_family_of_maximal_invariant H P z p hP hPH hzP (by omega) hmax

end CFSG.ShultStronglyClosedTI
