module

public import CFSG.RankThree.Coprime.HighTwoRankOddKernel
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.Coprime

open Subgroup CFSG

universe u

theorem layer_eq_top_of_isQuasisimple {M : Type*} [Group M] (hM : IsQuasisimple M) :
    layer M = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hM

theorem evenRank_le_of_pRank_le {Y : Type*} [Group Y] [Finite Y] {m : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r Y ≤ m) : CFSG.Assembly.evenRank Y ≤ m := by
  apply csSup_le'
  rintro _ ⟨r, H, hr, hr2, -, rfl⟩
  calc CFSG.Assembly.pRank r H = CFSG.Open.pRank r H := rfl
    _ ≤ CFSG.Open.pRank r (⊤ : Subgroup Y) := CFSG.SectionRank.pRank_mono hr.one_lt le_top
    _ = pRank r Y := (CFSG.SectionRank.pRank_eq_open_pRank_top r Y).symm
    _ ≤ m := h r hr hr2

theorem isElementaryAbelian_map_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (e : A ≃* B) {U : Subgroup A} (hU : IsElementaryAbelian p U) :
    IsElementaryAbelian p (U.map e.toMonoidHom) ∧
      Nat.card (U.map e.toMonoidHom) = Nat.card U :=
  ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr
      (CFSG.SectionRank.isElemAbelian_map
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).mp hU) e.toMonoidHom),
    Subgroup.card_map_of_injective e.injective⟩

theorem even_center_section_small_rank_central_cover {G : Type u} [Group G] [Finite G] (m : ℕ)
    (he : CFSG.Assembly.evenRank G ≤ m) {M : Type*} [Group M] [Finite M] (hM : IsQuasisimple M)
    (hZ : Even (Nat.card (center M)))
    (hS : ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2))
    (H : Subgroup G) (π : H →* M) (hπ : Function.Surjective π) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y) (_ : Group.IsPerfect Y)
      (φ : Y →* M ⧸ center M), Function.Surjective φ ∧ φ.ker ≤ center Y ∧
        ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r Y ≤ m := by
  classical
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* M := π.comp K.subtype with hπK
  have hπKs : Function.Surjective πK := by
    intro x
    have hx : x ∈ K.map π := by
      rw [hKmin.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin : ∀ Y : Subgroup K, Y ≠ ⊤ → Y.map πK ≠ ⊤ := by
    intro Y hY hYmap
    apply hY
    have h1 : (Y.map K.subtype).map π = ⊤ := by
      rw [Subgroup.map_map]
      exact hYmap
    have h2 := hKmin.le_of_le h1 (Subgroup.map_subtype_le Y)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ :=
    CFSG.SectionRank.minimal_semisimple_cover (layer_eq_top_of_isQuasisimple hM) πK hπKs hmin
  set C : Subgroup K := (center M).comap πK with hC
  have hCZ : Function.Surjective ((πK.comp C.subtype).codRestrict (center M)
      (fun x => x.2)) := by
    intro z
    obtain ⟨k, hk⟩ := hπKs z
    exact ⟨⟨k, show πK k ∈ center M by rw [hk]; exact z.2⟩, Subtype.ext hk⟩
  have h2C : 2 ∣ Nat.card C :=
    (even_iff_two_dvd.mp hZ).trans (Subgroup.card_dvd_of_surjective hCZ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Sylow 2 C := default with hT
  set R : Subgroup K := (T : Subgroup C).map C.subtype with hR
  have hRn : R.Normal := hCsyl 2 T
  have hRp : IsPGroup 2 R := T.isPGroup'.map _
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRne : R ≠ ⊥ := by
    rw [hR, Ne, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective]
    exact T.ne_bot_of_dvd_card h2C
  set ι : K →* G := H.subtype.comp K.subtype with hι
  have hιinj : Function.Injective ι := H.subtype_injective.comp K.subtype_injective
  set N := normalizer ((R.map ι : Subgroup G) : Set G) with hN
  have hloc : CFSG.Open.IsTwoLocal N := by
    refine ⟨R.map ι, ?_, hRp.map ι, rfl⟩
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj]
    exact hRne
  have hKN : (⊤ : Subgroup K).map ι ≤ N := by
    rintro _ ⟨k, -, rfl⟩
    rw [mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨k * x * k⁻¹, hRn.conj_mem x hx k, by simp [map_mul, map_inv]⟩
    · rintro ⟨x, hx, hxg⟩
      refine ⟨k⁻¹ * x * k, by simpa using hRn.conj_mem x hx k⁻¹, ?_⟩
      have h := congrArg (fun y => (ι k)⁻¹ * y * ι k) hxg
      simp only [map_mul, map_inv] at h ⊢
      rw [h]
      group
  have hKrank : ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r K ≤ m := by
    intro r hr hr2
    calc pRank r K = CFSG.Open.pRank r (⊤ : Subgroup K) :=
          CFSG.SectionRank.pRank_eq_open_pRank_top r K
      _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup K).map ι) :=
          CFSG.SectionRank.pRank_le_map hr.one_lt ι hιinj ⊤
      _ ≤ CFSG.Open.pRank r N := CFSG.SectionRank.pRank_mono hr.one_lt hKN
      _ ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 N hloc
      _ = CFSG.Assembly.evenRank G := rfl
      _ ≤ m := he
  have hRr : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card R := by
    intro r hr hr2 hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hYrank : ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r (K ⧸ R) ≤ m := fun r hr hr2 => by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr R
      (hRr r hr hr2)]
    exact hKrank r hr hr2
  have hRker : R ≤ ((QuotientGroup.mk' (center M)).comp πK).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hRC hx
  set φ : K ⧸ R →* M ⧸ center M :=
    QuotientGroup.lift R ((QuotientGroup.mk' (center M)).comp πK) hRker with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center M) q
    obtain ⟨k, rfl⟩ := hπKs x
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hφker : φ.ker = C.map (QuotientGroup.mk' R) := by
    rw [hφ, QuotientGroup.ker_lift, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  refine ⟨K ⧸ R, inferInstance, inferInstance, inferInstance, φ, hφs, ?_, hYrank⟩
  have hYperf : Group.IsPerfect (K ⧸ R) := inferInstance
  have hYe : CFSG.Assembly.evenRank (K ⧸ R) ≤ m := evenRank_le_of_pRank_le hYrank
  have hkernil : Group.IsNilpotent φ.ker := by
    rw [hφker]
    exact Group.nilpotent_of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective C)
  have hkerodd : Odd (Nat.card φ.ker) := by
    rw [hφker, CFSG.natCard_map_mk'_eq]
    have hsub : R.subgroupOf C = (T : Subgroup C) := by
      rw [hR, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
    rw [hsub, ← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)
  set iso := QuotientGroup.quotientKerEquivOfSurjective φ hφs with hiso
  have : IsSimpleGroup (M ⧸ center M) := hM.2.1
  have hsimple : IsSimpleGroup ((K ⧸ R) ⧸ φ.ker) := iso.isSimpleGroup
  have hnonab : ∃ a b : (K ⧸ R) ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hM.2.2
    refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
    have := congrArg iso h
    simpa using this
  obtain ⟨U, hU, hUcard⟩ := hS
  obtain ⟨hU', hUcard'⟩ := isElementaryAbelian_map_mulEquiv iso.symm hU
  exact high_two_rank_simple_odd_kernel_centralization m hYperf hYe φ.ker hkernil hkerodd hsimple
    hnonab ⟨_, hU', hUcard'.trans hUcard⟩

end CFSG.RankThree.Coprime
