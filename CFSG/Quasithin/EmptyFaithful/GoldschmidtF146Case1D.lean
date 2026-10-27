module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1A
public import CFSG.Quasithin.Background.GoldschmidtS146RQuot

public section

namespace CFSG.Quasithin.F146Field.Case1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.GoldS146R

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_imgJ_of_le {H J K S : Subgroup G} [(J.subgroupOf H).Normal]
    (hJ : IsPGroup 2 ↥J) (hKH : K ≤ H) (hS : IsSylowTwoOf S K) :
    IsSylowTwoOf (imgJ H J S) (imgJ H J K) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨imgJ_mono hS.1, ?_, ?_⟩
  · exact (A4.isPGroup_subgroupOf_of_le (hS.1.trans hKH) hS.2.1).map _
  · intro P hPK hP hSP
    set π := QuotientGroup.mk' (J.subgroupOf H) with hπ
    set P' : Subgroup G := (P.comap π).map H.subtype ⊓ K with hP'
    have hP'K : P' ≤ K := inf_le_right
    have hSP' : S ≤ P' := by
      intro s hs
      have hsK : s ∈ K := hS.1 hs
      refine ⟨⟨⟨s, hKH hsK⟩, ?_, rfl⟩, hsK⟩
      exact hSP (mem_imgJ.mpr ⟨⟨s, hKH hsK⟩, hs, rfl⟩)
    have hP'2 : IsPGroup 2 ↥P' := by
      rintro ⟨x, ⟨⟨h, hhP, rfl⟩, hxK⟩⟩
      obtain ⟨k, hk⟩ := hP ⟨π h, hhP⟩
      have h1 : π h ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have h2 : (h ^ 2 ^ k : ↥H) ∈ J.subgroupOf H := by
        rw [← QuotientGroup.eq_one_iff]
        show π (h ^ 2 ^ k) = 1
        rw [map_pow]
        exact h1
      have h3 : ((h : G) ^ 2 ^ k) ∈ J := by
        have := Subgroup.mem_subgroupOf.mp h2
        simpa using this
      obtain ⟨j, hj⟩ := hJ ⟨(h : G) ^ 2 ^ k, h3⟩
      refine ⟨k + j, Subtype.ext ?_⟩
      have := congrArg Subtype.val hj
      simpa [pow_add, pow_mul] using this
    have hle := ((A4.isSylowTwoOf_iff_maximal).mp hS).2.2 P' hP'K hP'2 hSP'
    intro p hp
    obtain ⟨h, hhK, rfl⟩ := mem_imgJ.mp (hPK hp)
    have : (h : G) ∈ P' := ⟨⟨h, hp, rfl⟩, hhK⟩
    exact mem_imgJ.mpr ⟨h, hle this, rfl⟩

omit [Finite G] in
theorem borel_eq_of_sylow {Y : Type} [Group Y] [Finite Y] {Ks TK B S0 : Subgroup Y}
    (hTK : IsSylowTwoOf TK Ks) (hS0 : IsSylowTwoOf S0 Ks)
    (hB : B = Ks ⊓ Subgroup.normalizer (S0 : Set Y)) (hTKB : TK ≤ B) :
    B = Ks ⊓ Subgroup.normalizer (TK : Set Y) := by
  have hBK : B ≤ Ks := hB ▸ inf_le_left
  have hBN : B ≤ Subgroup.normalizer (S0 : Set Y) := hB ▸ inf_le_right
  have hSB : S0 ≤ B := hB ▸ le_inf hS0.1 Subgroup.le_normalizer
  have hnorm : (S0.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBN
  have hTKB' : IsSylowTwoOf TK B := A4.isSylowTwoOf_mono hTK hTKB hBK
  have h1 : S0 ≤ TK := A4.le_of_normal_of_isSylowTwoOf hTKB' hSB hnorm hS0.2.1
  have h2 : TK ≤ S0 := ((A4.isSylowTwoOf_iff_maximal).mp hS0).2.2 TK hTK.1 hTK.2.1 h1
  rw [hB, le_antisymm h2 h1]

theorem inf_eq_inf_normalizer {M₀ H K T : Subgroup G} (hmin : MinParabolic H T M₀)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hker : kerIn M₀ H = pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star M₀ H K) (E2.star M₀ H (M₀ ⊓ K))) :
    K ⊓ M₀ = K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have hTH : T ≤ H := hmin.isSylow.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hJ2 : IsPGroup 2 ↥(kerIn M₀ H) := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hJT : kerIn M₀ H ≤ T := by
    rw [hker]
    exact B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hJM : kerIn M₀ H ≤ M₀ := kerIn_le
  have hJH : kerIn M₀ H ≤ H := hJM.trans hmin.maximal.1.le
  have hS : IsSylowTwoOf (T ⊓ K) K := isSylowTwoOf_inf_cComp hmin.isSylow hK hHK
  have hSyl : IsSylowTwoOf (E2.star M₀ H (T ⊓ K)) (E2.star M₀ H K) :=
    isSylowTwoOf_imgJ_of_le hJ2 hKH hS
  obtain ⟨S0, hS0, hMKs⟩ := hB
  have hTKM : E2.star M₀ H (T ⊓ K) ≤ E2.star M₀ H (M₀ ⊓ K) :=
    imgJ_mono (inf_le_inf_right K hmin.le)
  have hBorel := borel_eq_of_sylow hSyl hS0 hMKs hTKM
  have hTKH : T ⊓ K ≤ H := inf_le_right.trans hKH
  have hMKH : M₀ ⊓ K ≤ H := inf_le_right.trans hKH
  ext x
  constructor
  · rintro ⟨hxK, hxM⟩
    refine ⟨hxK, ?_⟩
    have hxH : x ∈ H := hKH hxK
    have hπx : (QuotientGroup.mk ⟨x, hxH⟩ : ↥H ⧸ (kerIn M₀ H).subgroupOf H) ∈
        E2.star M₀ H (M₀ ⊓ K) := mem_imgJ.mpr ⟨⟨x, hxH⟩, ⟨hxM, hxK⟩, rfl⟩
    rw [hBorel] at hπx
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    have hyH : y ∈ H := hTH hy.1
    have h1 := (Subgroup.mem_normalizer_iff.mp hπx.2 _).mp
      (mem_imgJ.mpr ⟨⟨y, hyH⟩, hy, rfl⟩ : (QuotientGroup.mk ⟨y, hyH⟩ :
        ↥H ⧸ (kerIn M₀ H).subgroupOf H) ∈ E2.star M₀ H (T ⊓ K))
    have hconj : x * y * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)
    have h2 : (QuotientGroup.mk ⟨x * y * x⁻¹, hconj⟩ :
        ↥H ⧸ (kerIn M₀ H).subgroupOf H) ∈ E2.star M₀ H (T ⊓ K) := by
      have : (QuotientGroup.mk ⟨x * y * x⁻¹, hconj⟩ : ↥H ⧸ (kerIn M₀ H).subgroupOf H) =
          QuotientGroup.mk ⟨x, hxH⟩ * QuotientGroup.mk ⟨y, hyH⟩ *
            (QuotientGroup.mk ⟨x, hxH⟩)⁻¹ := rfl
      rw [this]
      exact h1
    have h3 := (mk_mem_imgJ hTKH hJH _).mp h2
    exact ⟨sup_le inf_le_left hJT h3, K.mul_mem (K.mul_mem hxK hy.2) (K.inv_mem hxK)⟩
  · rintro ⟨hxK, hxN⟩
    refine ⟨hxK, ?_⟩
    have hxH : x ∈ H := hKH hxK
    have hNx : (QuotientGroup.mk ⟨x, hxH⟩ : ↥H ⧸ (kerIn M₀ H).subgroupOf H) ∈
        Subgroup.normalizer ((E2.star M₀ H (T ⊓ K) :
          Subgroup (↥H ⧸ (kerIn M₀ H).subgroupOf H)) : Set (↥H ⧸ (kerIn M₀ H).subgroupOf H)) := by
      refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
      obtain ⟨w, hwTK, rfl⟩ := mem_imgJ.mp hz
      have hconj : x * w * x⁻¹ ∈ T ⊓ K := (Subgroup.mem_normalizer_iff.mp hxN w).mp hwTK
      have hconjH : x * (w : G) * x⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem hxH w.2) (H.inv_mem hxH)
      exact mem_imgJ.mpr ⟨⟨x * w * x⁻¹, hconjH⟩, hconj, rfl⟩
    have hmem : (QuotientGroup.mk ⟨x, hxH⟩ : ↥H ⧸ (kerIn M₀ H).subgroupOf H) ∈
        E2.star M₀ H (M₀ ⊓ K) := by
      rw [hBorel]
      exact ⟨mem_imgJ.mpr ⟨⟨x, hxH⟩, hxK, rfl⟩, hNx⟩
    have h3 := (mk_mem_imgJ hMKH hJH _).mp hmem
    exact sup_le inf_le_left hJM h3

theorem borel_property_cjSub {M₀ T K : Subgroup G} (hTM : T ≤ M₀) {s : G} (hs : s ∈ T)
    (hbor : ∀ x ∈ K, x ∈ M₀ → x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    {x : G} (hx : x ∈ cjSub s K) (hxM : x ∈ M₀) :
    x ∈ Subgroup.normalizer ((T ⊓ cjSub s K : Subgroup G) : Set G) := by
  rw [mem_cjSub] at hx
  have hy : s⁻¹ * x * s ∈ M₀ :=
    M₀.mul_mem (M₀.mul_mem (M₀.inv_mem (hTM hs)) hxM) (hTM hs)
  have hN := hbor _ hx hy
  refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
  obtain ⟨hzT, hz'⟩ := hz
  have hz'' : s⁻¹ * z * s ∈ K := mem_cjSub.mp hz'
  have hzK : s⁻¹ * z * s ∈ T ⊓ K := ⟨T.mul_mem (T.mul_mem (T.inv_mem hs) hzT) hs, hz''⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hN _).mp hzK
  have h2 : s * ((s⁻¹ * x * s) * (s⁻¹ * z * s) * (s⁻¹ * x * s)⁻¹) * s⁻¹ = x * z * x⁻¹ := by
    group
  refine ⟨?_, ?_⟩
  · rw [← h2]
    exact T.mul_mem (T.mul_mem hs h1.1) (T.inv_mem hs)
  · refine mem_cjSub.mpr ?_
    have : s⁻¹ * (x * z * x⁻¹) * s = (s⁻¹ * x * s) * (s⁻¹ * z * s) * (s⁻¹ * x * s)⁻¹ := by
      group
    rw [this]
    exact h1.2

end CFSG.Quasithin.F146Field.Case1
