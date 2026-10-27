module

import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofFactors
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec10.SuzukiSectionProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
open Subgroup

theorem normal_closure_of_conj {Y : Type*} [Group Y] {s : Set Y}
    (hs : ∀ g x, x ∈ s → g * x * g⁻¹ ∈ s) : (closure s).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have h1 : g * x * g⁻¹ ∈ (closure s).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [MonoidHom.map_closure] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨y, hy, rfl⟩
  exact hs g y hy

theorem closure_pow_three_normal {Y : Type*} [Group Y] {D : Subgroup Y} (hD : D.Normal) :
    (closure {x | x ∈ D ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}).Normal := by
  refine normal_closure_of_conj fun g x ⟨hxD, k, hk⟩ => ⟨hD.conj_mem x hxD g, k, ?_⟩
  rw [conj_pow, hk, mul_one, mul_inv_cancel]

theorem closure_pow_three_eq_top {P : Type*} [Group P] (hPq : IsQuasisimple P) {y : P}
    (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) (hyc : y ∉ center P) :
    closure {x : P | ∃ k : ℕ, x ^ 3 ^ k = 1} = ⊤ := by
  have hn : (closure {x : P | ∃ k : ℕ, x ^ 3 ^ k = 1}).Normal :=
    normal_closure_of_conj fun g x ⟨k, hk⟩ => ⟨k, by rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hPq
      (closure {x : P | ∃ k : ℕ, x ^ 3 ^ k = 1}) with h | h
  · exact absurd (h (subset_closure hy)) hyc
  · exact h

theorem exists_pow_three_not_mem_center {P : Type} [Group P] [Finite P]
    (htype : Sec4.IsSLThreePiAt P 4 ∨ Sec4.IsTripleCover P (alternatingGroup (Fin 6))) :
    ∃ y : P, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ y ∉ center P := by
  rcases htype with h4 | h6
  · have h4' : Sec4.IsSLThreePiAt P (2 ^ 2) := h4
    obtain ⟨y, hy3, hyc⟩ :=
      KFacts.exists_pow_three_eq_one_not_mem_center_of_isSLThreePiAt_two_pow (by norm_num) h4'
    exact ⟨y, ⟨1, by rw [pow_one]; exact hy3⟩, hyc⟩
  · obtain ⟨hc3, ⟨e⟩⟩ := h6
    have hmem : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    have hσ3 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
    have hσ1 : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2) ≠ 1 := by decide
    set c : alternatingGroup (Fin 6) := ⟨_, hmem⟩ with hc
    have hc3' : c ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hσ3)
    have hc1 : c ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm c)
    have hy3 : y ^ 3 ∈ center P := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy, ← map_pow, hc3', map_one]
    refine ⟨y, ⟨2, ?_⟩, fun h => hc1 ?_⟩
    · have h1 := pow_card_eq_one' (G := center P) (x := ⟨y ^ 3, hy3⟩)
      rw [hc3] at h1
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, h2]
    · have h1 : (y : P ⧸ center P) = 1 := (QuotientGroup.eq_one_iff y).mpr h
      rw [hy] at h1
      have h2 := congrArg e h1
      rwa [MulEquiv.apply_symm_apply, map_one] at h2

theorem exists_pow_three_lift {G : Type*} [Group G] [Finite G] {D S : Subgroup G}
    {σ : MulAut S} (hσ : σ ∈ Sec4.autIn D S) {k : ℕ} (hσk : σ ^ 3 ^ k = 1) :
    ∃ x ∈ D, ∃ hx : x ∈ normalizer (S : Set G), (∃ e : ℕ, x ^ 3 ^ e = 1) ∧
      S.normalizerMonoidHom ⟨x, hx⟩ = σ := by
  obtain ⟨g, hgN, hgD, hg⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨e, m, hm, hgm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hcop : m.Coprime (orderOf σ) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσk)
    rw [hj]
    exact Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨g ^ (m * u), pow_mem hgD _, pow_mem hgN _, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, show m * u * 3 ^ e = 3 ^ e * m * u by ring, pow_mul, ← hgm,
      pow_orderOf_eq_one, one_pow]
  · have h1 : (⟨g ^ (m * u), pow_mem hgN _⟩ : normalizer (S : Set G)) = ⟨g, hgN⟩ ^ (m * u) :=
      Subtype.ext (by simp)
    rw [h1, map_pow, hg, pow_mul, hu]

theorem autIn_inSubgroup_perfectResidual {G : Type*} [Group G] [Finite G] {O S : Subgroup G}
    (hOS : O ≤ normalizer (S : Set G)) :
    Sec4.autIn (inSubgroup perfectResidual O) S = inSubgroup perfectResidual (Sec4.autIn O S) := by
  set NS := normalizer (S : Set G) with hNS
  set J := inSubgroup perfectResidual O with hJdef
  have hJS : J ≤ NS := (map_subtype_le _).trans hOS
  set X := O.subgroupOf NS with hX
  have hXmap : X.map NS.subtype = O := Subgroup.map_subgroupOf_eq_of_le hOS
  have hJsub : J.subgroupOf NS = inSubgroup perfectResidual X := by
    have h1 := CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      NS.subtype NS.subtype_injective X
    rw [hXmap, ← hJdef] at h1
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective NS.subtype_injective]
  have h1 : Sec4.autIn J S = (J.subgroupOf NS).map S.normalizerMonoidHom := by
    rw [Sec4.autIn, inf_eq_left.mpr hJS]
  have h2 : Sec4.autIn O S = X.map S.normalizerMonoidHom := by
    rw [Sec4.autIn, inf_eq_left.mpr hOS]
  rw [h1, hJsub, KFacts.map_inSubgroup_perfectResidual_hom, h2]

theorem pRank_five_le_two {G : Type} [Group G] [Finite G] (hG : TheoremFourHyp G)
    {S : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) {N : Subgroup G}
    (hN : N ≤ normalizer (S : Set G)) : CFSG.Open.pRank 5 (⊤ : Subgroup N) ≤ 2 := by
  have h2loc : CFSG.Assembly.IsTwoLocal (normalizer (S : Set G)) := ⟨S, hS1, hS2, rfl⟩
  have hloc : CFSG.Open.pRank 5 (normalizer (S : Set G)) ≤
      CFSG.Assembly.RankThreeEven.localRank 5 G := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨_, h2loc, rfl⟩
    rintro _ ⟨Z, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card 5 (by norm_num) Z).trans
      (Subgroup.card_le_card_group Z)
  have hlt := hG.localRank_lt 5 (by norm_num) (by norm_num)
  have h1 := CFSG.SectionRank.pRank_le_map (p := 5) (by norm_num) N.subtype N.subtype_injective ⊤
  rw [← MonoidHom.range_eq_map, range_subtype] at h1
  have h3 := CFSG.SectionRank.pRank_mono (p := 5) (by norm_num) hN
  omega

end CFSG.RankThree.PartTwo.Sec10.SuzukiSectionProof

