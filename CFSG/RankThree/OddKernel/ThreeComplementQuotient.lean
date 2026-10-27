module

public import CFSG.RankThree.OddKernel.RankTwoPowerStructure
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

universe u

theorem exists_mul_mem_normalizer_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} (T : Sylow p H) {y : G} (hy : ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    ∃ h ∈ H, h * y ∈ normalizer (((T : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  let T' : Subgroup G := (T : Subgroup H).map H.subtype
  let K : Subgroup G := T'.map (MulAut.conj y).toMonoidHom
  have hT'H : T' ≤ H := map_subtype_le _
  have hKH : K ≤ H := by
    rintro _ ⟨t, ht, rfl⟩
    exact hy t (hT'H ht)
  have hKcard : Nat.card (K.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv,
      card_map_of_injective (MulAut.conj y).injective,
      card_map_of_injective H.subtype_injective, T.card_eq_multiplicity]
  let K₀ : Sylow p H := Sylow.ofCard (K.subgroupOf H) hKcard
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H K₀ T
  have hTeq : (T : Subgroup H) = MulAut.conj h • K.subgroupOf H := by
    rw [← hh]
    rfl
  have hmem : ∀ x : G, x ∈ T' ↔ ∃ t ∈ T', x = (h : G) * (y * t * y⁻¹) * (h : G)⁻¹ := by
    intro x
    constructor
    · rintro ⟨x', hx', rfl⟩
      have hx'' : x' ∈ (MulAut.conj h • K.subgroupOf H : Subgroup H) := hTeq ▸ hx'
      rw [mem_smul_pointwise_iff_exists] at hx''
      obtain ⟨k, hk, hkx⟩ := hx''
      obtain ⟨t, ht, htk⟩ := (mem_subgroupOf.1 hk : (k : G) ∈ K)
      refine ⟨t, ht, ?_⟩
      rw [← hkx]
      change (h : G) * k * (h : G)⁻¹ = _
      rw [← htk]
      rfl
    · rintro ⟨t, ht, rfl⟩
      have hk : y * t * y⁻¹ ∈ K := ⟨t, ht, rfl⟩
      have hkH : y * t * y⁻¹ ∈ H := hKH hk
      have hx : (⟨(h : G) * (y * t * y⁻¹) * (h : G)⁻¹,
          H.mul_mem (H.mul_mem h.2 hkH) (H.inv_mem h.2)⟩ : H) ∈ (T : Subgroup H) := by
        have : (⟨(h : G) * (y * t * y⁻¹) * (h : G)⁻¹,
            H.mul_mem (H.mul_mem h.2 hkH) (H.inv_mem h.2)⟩ : H) ∈
            (MulAut.conj h • K.subgroupOf H : Subgroup H) := by
          rw [mem_smul_pointwise_iff_exists]
          exact ⟨⟨_, hkH⟩, mem_subgroupOf.2 hk, rfl⟩
        exact hTeq ▸ this
      exact ⟨_, hx, rfl⟩
  refine ⟨h, h.2, ?_⟩
  rw [mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [hmem]
    exact ⟨n, hn, by group⟩
  · intro hn
    rw [hmem] at hn
    obtain ⟨t, ht, htn⟩ := hn
    have : n = t := by
      have h2 : (h : G) * y * n * (y⁻¹ * (h : G)⁻¹) = (h : G) * y * t * (y⁻¹ * (h : G)⁻¹) := by
        rw [← mul_inv_rev, htn]
        group
      exact mul_left_cancel (mul_right_cancel h2)
    exact this ▸ ht

theorem sylow_preimage_map_normalizer {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] (U : Subgroup (G ⧸ N)) (hU : IsPGroup 2 U)
    (T : Sylow 2 (U.comap (QuotientGroup.mk' N))) :
    let T' : Subgroup G := (T : Subgroup (U.comap (QuotientGroup.mk' N))).map
      (U.comap (QuotientGroup.mk' N)).subtype
    T'.map (QuotientGroup.mk' N) = U ∧
      (normalizer (T' : Set G)).map (QuotientGroup.mk' N) = normalizer (U : Set (G ⧸ N)) ∧
      ((QuotientGroup.mk' N).domRestrict (normalizer (T' : Set G))).ker =
        N.subgroupOf (normalizer (T' : Set G)) := by
  intro T'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective ((QuotientGroup.mk' N).subgroupComap U) :=
    (QuotientGroup.mk' N).subgroupComap_surjective U (QuotientGroup.mk'_surjective N)
  have hQ : ((T.mapSurjective hf : Sylow 2 U) : Subgroup U) = ⊤ :=
    ((T.mapSurjective hf).is_maximal' (hU.to_subgroup ⊤) le_top).symm
  have hmapT : T'.map (QuotientGroup.mk' N) = U := by
    have h1 : T'.map (QuotientGroup.mk' N) =
        ((T : Subgroup _).map ((QuotientGroup.mk' N).subgroupComap U)).map U.subtype := by
      rw [map_map, map_map]
      rfl
    rw [h1, ← Sylow.coe_mapSurjective hf, hQ, ← MonoidHom.range_eq_map, range_subtype]
  have hle : (normalizer (T' : Set G)).map (QuotientGroup.mk' N) ≤
      normalizer (U : Set (G ⧸ N)) := by
    have h := le_normalizer_map (H := T') (QuotientGroup.mk' N)
    rwa [hmapT] at h
  refine ⟨hmapT, le_antisymm hle ?_, by rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']⟩
  intro z hz
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
  have hy : ∀ h ∈ U.comap (QuotientGroup.mk' N),
      y * h * y⁻¹ ∈ U.comap (QuotientGroup.mk' N) := by
    intro h hh
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hz _).1 hh
  obtain ⟨h, hhH, hhy⟩ := exists_mul_mem_normalizer_of_sylow T hy
  have hρh : QuotientGroup.mk' N h ∈ T'.map (QuotientGroup.mk' N) := hmapT ▸ hhH
  obtain ⟨t, htT, hth⟩ := mem_map.1 hρh
  refine ⟨t⁻¹ * (h * y), mul_mem (inv_mem (le_normalizer htT)) hhy, ?_⟩
  rw [map_mul, map_mul, map_inv, hth, inv_mul_cancel_left]

theorem pRank_le_three_of_surjective {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {M L : Type*}
    [Group M] [Group L] [Finite M] [Finite L] (ψ : M →* L) (hψ : Function.Surjective ψ)
    (hM : pRank p M ≤ 2) : pRank p L ≤ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow p M) := inferInstance
  have hP₀rank : pRank p (P₀ : Subgroup M) ≤ 2 := (pRank_sylow P₀).2 ▸ hM
  have e : (P₀ : Subgroup M) ⧸ (ψ.domRestrict (P₀ : Subgroup M)).ker ≃*
      ((P₀.mapSurjective hψ : Sylow p L) : Subgroup L) :=
    (QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr
      ((MonoidHom.domRestrict_range _ _).trans (Sylow.coe_mapSurjective hψ P₀).symm))
  rw [← (pRank_sylow (P₀.mapSurjective hψ)).2, pRank_eq_open_pRank_top,
    ← pRank_top_eq_of_mulEquiv hp.one_lt e, ← pRank_eq_open_pRank_top]
  exact rank_two_large_prime_quotient_pRank_le_three hp hp3 P₀.isPGroup' hP₀rank _

theorem pRank_normalizer_le_localRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {T : Subgroup G} (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 T) :
    pRank p (normalizer (T : Set G)) ≤ localRank p G := by
  rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
  exact CFSG.RankThree.Classical.pRank_le_localRank hp ⟨T, hT0, hT2, rfl⟩

theorem localRank_quotient_le_three {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (N : Subgroup G) [N.Normal] (hloc : localRank p G ≤ 2) :
    localRank p (G ⧸ N) ≤ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine csSup_le' ?_
  rintro k ⟨H, ⟨U, hU0, hU2, rfl⟩, rfl⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 (U.comap (QuotientGroup.mk' N))) := inferInstance
  have hlift := sylow_preimage_map_normalizer N U hU2 T
  obtain ⟨hmapT, hnorm, -⟩ := hlift
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup G, T' = (T : Subgroup (U.comap (QuotientGroup.mk' N))).map
      (U.comap (QuotientGroup.mk' N)).subtype := ⟨_, rfl⟩
  rw [← hT'] at hmapT hnorm
  have hT'2 : IsPGroup 2 T' := hT' ▸ T.isPGroup'.map _
  have hT'0 : T' ≠ ⊥ := fun h => hU0 (by rw [← hmapT, h, Subgroup.map_bot])
  let ψ := ((QuotientGroup.mk' N).domRestrict (normalizer (T' : Set G))).codRestrict
      (normalizer (U : Set (G ⧸ N))) (fun x => hnorm ▸ mem_map_of_mem _ x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hnorm] at hz
    obtain ⟨m, hm, rfl⟩ := mem_map.1 hz
    exact ⟨⟨m, hm⟩, rfl⟩
  have h := pRank_le_three_of_surjective hp hp3 ψ hψ
    ((pRank_normalizer_le_localRank hp.one_lt hT'0 hT'2).trans hloc)
  change CFSG.Open.pRank p (normalizer (U : Set (G ⧸ N))) ≤ 3
  rwa [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]

theorem localRank_le_evenRank {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : localRank r G ≤ CFSG.Assembly.evenRank G := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  exact le_csSup ⟨Nat.card G, by
      rintro _ ⟨q, K, hq, -, -, rfl⟩
      exact CFSG.RankThree.Classical.pRank_le_natCard hq.one_lt K⟩
    ⟨r, H, hr, hr2, hH, rfl⟩

theorem evenRank_le_of_localRank_le {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → localRank r G ≤ m) : CFSG.Assembly.evenRank G ≤ m := by
  refine csSup_le' ?_
  rintro _ ⟨r, H, hr, hr2, hH, rfl⟩
  exact (CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt hH).trans (h r hr hr2)

theorem evenRank_eq_twoLocalOddRank (G : Type*) [Group G] [Finite G] :
    CFSG.Assembly.evenRank G = CFSG.twoLocalOddRank G :=
  CFSG.SectionRank.assembly_evenRank_eq_twoLocalOddRank G

theorem rank_three_three_complement_quotient_sharp_local_bounds {G : Type u} [Group G]
    [Finite G] (N : Subgroup G) [N.Normal] :
    (∀ U : Subgroup (G ⧸ N), IsPGroup 2 U → ∀ T : Sylow 2 (U.comap (QuotientGroup.mk' N)),
      let T' : Subgroup G := (T : Subgroup (U.comap (QuotientGroup.mk' N))).map
        (U.comap (QuotientGroup.mk' N)).subtype
      T'.map (QuotientGroup.mk' N) = U ∧
        (normalizer (T' : Set G)).map (QuotientGroup.mk' N) = normalizer (U : Set (G ⧸ N)) ∧
        ((QuotientGroup.mk' N).domRestrict (normalizer (T' : Set G))).ker =
          N.subgroupOf (normalizer (T' : Set G))) ∧
    (∀ p : ℕ, p.Prime → 3 < p → localRank p G ≤ 2 → localRank p (G ⧸ N) ≤ 3) ∧
    (¬ 3 ∣ Nat.card N → CFSG.twoLocalOddRank G ≤ 3 →
      (∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) →
      CFSG.twoLocalOddRank (G ⧸ N) ≤ 3 ∧ CFSG.Assembly.evenRank (G ⧸ N) ≤ 3 ∧
        localRank 3 (G ⧸ N) ≤ localRank 3 G ∧ localRank 3 G ≤ 3 ∧
        ∀ r : ℕ, r.Prime → 3 < r →
          (¬ r ∣ Nat.card N → localRank r (G ⧸ N) ≤ 2) ∧ localRank r (G ⧸ N) ≤ 3) := by
  refine ⟨fun U hU T => sylow_preimage_map_normalizer N U hU T,
    fun p hp hp3 hloc => localRank_quotient_le_three hp hp3 N hloc, fun h3 he' hr => ?_⟩
  have he : CFSG.Assembly.evenRank G ≤ 3 := (evenRank_eq_twoLocalOddRank G) ▸ he'
  have h33 : localRank 3 (G ⧸ N) ≤ localRank 3 G :=
    CFSG.RankThree.Classical2.localRank_quotient_le Nat.prime_three (by norm_num) N h3
  have h3G : localRank 3 G ≤ 3 :=
    (localRank_le_evenRank Nat.prime_three (by norm_num)).trans he
  have hbig : ∀ r : ℕ, r.Prime → 3 < r → localRank r (G ⧸ N) ≤ 3 := fun r hr' hr3 =>
    localRank_quotient_le_three hr' hr3 N (hr r hr' hr3)
  have hX : CFSG.Assembly.evenRank (G ⧸ N) ≤ 3 := by
    refine evenRank_le_of_localRank_le fun r hr' hr2 => ?_
    rcases (show r = 3 ∨ 3 < r by
      have := hr'.two_le
      rcases (show r = 2 ∨ r = 3 ∨ 3 < r by omega) with h | h | h
      · exact absurd h hr2
      · exact Or.inl h
      · exact Or.inr h) with rfl | hr3
    · exact h33.trans h3G
    · exact hbig r hr' hr3
  refine ⟨(evenRank_eq_twoLocalOddRank (G ⧸ N)) ▸ hX, hX, h33, h3G, fun r hr' hr3 =>
    ⟨fun hrN => (CFSG.RankThree.Classical2.localRank_quotient_le hr' (by omega) N hrN).trans
      (hr r hr' hr3), hbig r hr' hr3⟩⟩

theorem rank_three_three_complement_quotient_sharp_local_bounds_theta {G : Type u} [Group G]
    [Finite G] (he : CFSG.twoLocalOddRank G ≤ 3)
    (hr : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) :
    let N := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 G
    N.Normal ∧ ¬ 3 ∣ Nat.card N ∧
      CFSG.twoLocalOddRank (G ⧸ N) ≤ 3 ∧ CFSG.Assembly.evenRank (G ⧸ N) ≤ 3 ∧
      localRank 3 (G ⧸ N) ≤ localRank 3 G ∧ localRank 3 G ≤ 3 ∧
      ∀ r : ℕ, r.Prime → 3 < r →
        (¬ r ∣ Nat.card N → localRank r (G ⧸ N) ≤ 2) ∧ localRank r (G ⧸ N) ≤ 3 := by
  intro N
  have h3 : ¬ 3 ∣ Nat.card N :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      Nat.prime_three).2.2.1
  have h := (rank_three_three_complement_quotient_sharp_local_bounds N).2.2 h3 he hr
  exact ⟨inferInstance, h3, h⟩

end CFSG.RankThree.OddKernel
