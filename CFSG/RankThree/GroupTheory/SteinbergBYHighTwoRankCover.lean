module

public import CFSG.RankThree.Coprime.EvenCenterSectionCover
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG Subgroup

universe u

theorem twoLocalOddRank_eq_evenRank (G : Type*) [Group G] [Finite G] :
    twoLocalOddRank G = CFSG.Assembly.evenRank G :=
  (CFSG.SectionRank.assembly_evenRank_eq_twoLocalOddRank G).symm

theorem high_two_rank_simple_section_small_rank_central_cover {G : Type u} [Group G] [Finite G]
    (m : ℕ) (he : twoLocalOddRank G ≤ m) {S : Type*} [Group S] [Finite S]
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hS : ∃ U : Subgroup S, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (m + 2))
    (H : Subgroup G) (π : H →* S) (hπ : Function.Surjective π) :
    ∃ (Y : Type u) (_ : Group Y) (_ : Finite Y), Group.IsPerfect Y ∧
      ∃ φ : Y →* S, Function.Surjective φ ∧ φ.ker ≤ center Y ∧ twoLocalOddRank Y ≤ m := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he' : CFSG.Assembly.evenRank G ≤ m := twoLocalOddRank_eq_evenRank G ▸ he
  obtain ⟨hSq, hSZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hSnab
  have hfinish : ∀ (Y : Type u) [Group Y] [Finite Y], Group.IsPerfect Y → ∀ φ : Y →* S,
      Function.Surjective φ → Group.IsNilpotent φ.ker → Odd (Nat.card φ.ker) →
      CFSG.Assembly.evenRank Y ≤ m → φ.ker ≤ center Y := by
    intro Y _ _ hYp φ hφs hnil hodd hYe
    set iso := QuotientGroup.quotientKerEquivOfSurjective φ hφs
    have hsimple : IsSimpleGroup (Y ⧸ φ.ker) := iso.isSimpleGroup
    have hnonab : ∃ a b : Y ⧸ φ.ker, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hSnab
      refine ⟨iso.symm a, iso.symm b, fun h => hab ?_⟩
      have := congrArg iso h
      simpa using this
    obtain ⟨U, hU, hUcard⟩ := hS
    obtain ⟨hU', hUcard'⟩ := RankThree.Coprime.isElementaryAbelian_map_mulEquiv iso.symm hU
    exact RankThree.Coprime.high_two_rank_simple_odd_kernel_centralization m hYp hYe φ.ker hnil
      hodd hsimple hnonab ⟨_, hU', hUcard'.trans hUcard⟩
  obtain ⟨K, -, hKmin⟩ := Finite.exists_le_minimal (p := fun K : Subgroup H => K.map π = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective π hπ])
  set πK : K →* S := π.comp K.subtype with hπK
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
  obtain ⟨hKperf, hCn, hCnil, hCsyl, -, -, -, -, -⟩ := SectionRank.minimal_semisimple_cover
    (RankThree.Coprime.layer_eq_top_of_isQuasisimple hSq) πK hπKs hmin
  set C : Subgroup K := (center S).comap πK with hC
  have hCker : πK.ker = C := by rw [hC, hSZ, MonoidHom.comap_bot]
  set T : Sylow 2 C := default with hT
  set R : Subgroup K := (T : Subgroup C).map C.subtype with hR
  have hRn : R.Normal := hCsyl 2 T
  have hRp : IsPGroup 2 R := T.isPGroup'.map _
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  set ι : K →* G := H.subtype.comp K.subtype with hι
  have hιinj : Function.Injective ι := H.subtype_injective.comp K.subtype_injective
  by_cases hRbot : R = ⊥
  ·
    have hTbot : (T : Subgroup C) = ⊥ := by
      rw [hR, Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective] at hRbot
      exact hRbot
    have hCodd : Odd (Nat.card C) := by
      have h := Subgroup.card_mul_index (T : Subgroup C)
      have hidx : ¬ 2 ∣ (T : Subgroup C).index := T.not_dvd_index
      rw [hTbot, Subgroup.card_bot, one_mul] at h
      rw [hTbot] at hidx
      rw [← h]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hidx)
    have hKe : CFSG.Assembly.evenRank K ≤ m := by
      refine csSup_le' ?_
      rintro _ ⟨r, _, hr, hr2, ⟨A, hA1, hA2, rfl⟩, rfl⟩
      have hloc : CFSG.Open.IsTwoLocal (normalizer ((A.map ι : Subgroup G) : Set G)) :=
        ⟨A.map ι, by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj], hA2.map ι, rfl⟩
      calc CFSG.Assembly.pRank r (normalizer (A : Set K)) =
            CFSG.Open.pRank r (normalizer (A : Set K)) := rfl
        _ ≤ CFSG.Open.pRank r ((normalizer (A : Set K)).map ι) :=
            SectionRank.pRank_le_map hr.one_lt ι hιinj _
        _ ≤ CFSG.Open.pRank r (normalizer ((A.map ι : Subgroup G) : Set G)) :=
            SectionRank.pRank_mono hr.one_lt (Subgroup.le_normalizer_map ι)
        _ ≤ CFSG.Open.evenRank G :=
            RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 _ hloc
        _ = CFSG.Assembly.evenRank G := rfl
        _ ≤ m := he'
    refine ⟨K, inferInstance, inferInstance, hKperf, πK, hπKs, ?_, ?_⟩
    · refine hfinish K hKperf πK hπKs (hCker ▸ hCnil) (hCker ▸ hCodd) hKe
    · rw [twoLocalOddRank_eq_evenRank]
      exact hKe
  ·
    set N := normalizer ((R.map ι : Subgroup G) : Set G) with hN
    have hloc : CFSG.Open.IsTwoLocal N := by
      refine ⟨R.map ι, ?_, hRp.map ι, rfl⟩
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hιinj]
      exact hRbot
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
            SectionRank.pRank_eq_open_pRank_top r K
        _ ≤ CFSG.Open.pRank r ((⊤ : Subgroup K).map ι) :=
            SectionRank.pRank_le_map hr.one_lt ι hιinj ⊤
        _ ≤ CFSG.Open.pRank r N := SectionRank.pRank_mono hr.one_lt hKN
        _ ≤ CFSG.Open.evenRank G :=
            RankThreeEvenClassification.Helpers.pRank_le_evenRank r hr hr2 N hloc
        _ = CFSG.Assembly.evenRank G := rfl
        _ ≤ m := he'
    have hRr : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card R := by
      intro r hr hr2 hdvd
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
      rw [hk] at hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
    have hYrank : ∀ r : ℕ, r.Prime → r ≠ 2 → pRank r (K ⧸ R) ≤ m := fun r hr hr2 => by
      rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hr R
        (hRr r hr hr2)]
      exact hKrank r hr hr2
    have hRker : R ≤ πK.ker := hCker ▸ hRC
    set φ : K ⧸ R →* S := QuotientGroup.lift R πK hRker with hφ
    have hφs : Function.Surjective φ := by
      intro q
      obtain ⟨k, rfl⟩ := hπKs q
      exact ⟨QuotientGroup.mk k, rfl⟩
    have hφker : φ.ker = C.map (QuotientGroup.mk' R) := by
      rw [hφ, QuotientGroup.ker_lift, hCker]
    have hYe : CFSG.Assembly.evenRank (K ⧸ R) ≤ m :=
      RankThree.Coprime.evenRank_le_of_pRank_le hYrank
    have hkernil : Group.IsNilpotent φ.ker := by
      rw [hφker]
      exact Group.nilpotent_of_surjective _ ((QuotientGroup.mk' R).subgroupMap_surjective C)
    have hkerodd : Odd (Nat.card φ.ker) := by
      rw [hφker, CFSG.natCard_map_mk'_eq]
      have hsub : R.subgroupOf C = (T : Subgroup C) := by
        rw [hR, subgroupOf, comap_map_eq_self_of_injective C.subtype_injective]
      rw [hsub, ← Subgroup.index_eq_card]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp T.not_dvd_index)
    have hYperf : Group.IsPerfect (K ⧸ R) := inferInstance
    refine ⟨K ⧸ R, inferInstance, inferInstance, hYperf, φ, hφs,
      hfinish (K ⧸ R) hYperf φ hφs hkernil hkerodd hYe, ?_⟩
    rw [twoLocalOddRank_eq_evenRank]
    exact hYe

end CFSG.RankThree.GroupTheory.SteinbergBY
