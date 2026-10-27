module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPBar
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem exists_isBarMap {H C : Subgroup G} (hC : (C.subgroupOf H).Normal) :
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (φ : ↥H →* Q), IsBarMap H C φ := by
  haveI : (C.subgroupOf H).Normal := hC
  let Q := ↥H ⧸ (C.subgroupOf H)
  haveI : Finite Q := by infer_instance
  refine ⟨Q, inferInstance, by infer_instance, QuotientGroup.mk' (C.subgroupOf H), ?_⟩
  refine ⟨QuotientGroup.mk'_surjective (C.subgroupOf H), ?_⟩
  intro k
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf

section Pull

variable {H C : Subgroup G} {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}

theorem a_le_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {T A : Subgroup G} (hAH : A ≤ H)
    {Lb Kb : Subgroup Q}
    (h : ∀ x ∈ barSub H φ A, ∃ k ∈ Kb, ∃ t ∈ cenTMod (⊥ : Subgroup Q) Lb (barSub H φ T),
      (k * t)⁻¹ * x ∈ (⊥ : Subgroup Q)) :
    ∀ x ∈ A, ∃ k ∈ barPre H φ Kb, ∃ t ∈ cenTMod C (barPre H φ Lb) T,
      (k * t)⁻¹ * x ∈ C := by
  intro x hx
  have hxH : x ∈ H := hAH hx
  have hxbar : φ ⟨x, hxH⟩ ∈ barSub H φ A :=
    mem_barSub.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
  obtain ⟨kb, hkbKb, tb, htb, hker⟩ := h (φ ⟨x, hxH⟩) hxbar
  obtain ⟨k, hk⟩ := hφ.surjective kb
  obtain ⟨tbH, htbT, htbφ⟩ := mem_barSub.mp htb.1
  have htcen : (tbH : G) ∈ cenTMod C (barPre H φ Lb) T := by
    constructor
    · exact htbT
    · intro l hl
      obtain ⟨hlH, hlLb⟩ := mem_barPre.mp hl
      have hcomm : tb * (φ ⟨l, hlH⟩) * tb⁻¹ * (φ ⟨l, hlH⟩)⁻¹ = 1 := by
        have := htb.2 (φ ⟨l, hlH⟩) hlLb
        rwa [Subgroup.mem_bot] at this
      have hmem : φ (tbH * ⟨l, hlH⟩ * tbH⁻¹ * ⟨l, hlH⟩⁻¹) = 1 := by
        simp only [map_mul, map_inv, htbφ]
        exact hcomm
      have := (hφ.ker_iff (tbH * ⟨l, hlH⟩ * tbH⁻¹ * ⟨l, hlH⟩⁻¹)).mp hmem
      simpa using this
  refine ⟨(k : G), ?_, (tbH : G), htcen, ?_⟩
  · rw [mem_barPre]
    exact ⟨k.2, by rwa [hk]⟩
  · have hker2 : φ ((k * tbH)⁻¹ * ⟨x, hxH⟩) = 1 := by
      simp only [map_mul, map_inv, hk, htbφ]
      have := hker
      rwa [Subgroup.mem_bot] at this
    have := (hφ.ker_iff ((k * tbH)⁻¹ * ⟨x, hxH⟩)).mp hker2
    simpa using this

theorem b_not_le_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {T A : Subgroup G} (hAH : A ≤ H)
    {Lb Kb : Subgroup Q}
    (h : ¬ ∀ x ∈ barSub H φ A, ∃ o ∈ oTwoMod (⊥ : Subgroup Q) Kb,
      ∃ t ∈ cenTMod (⊥ : Subgroup Q) Lb (barSub H φ T), (o * t)⁻¹ * x ∈ (⊥ : Subgroup Q)) :
    ¬ ∀ x ∈ A, ∃ o ∈ oTwoMod C (barPre H φ Kb), ∃ t ∈ cenTMod C (barPre H φ Lb) T,
      (o * t)⁻¹ * x ∈ C := by
  intro hG
  apply h
  intro xbar hxbar
  obtain ⟨x, hxA, rfl⟩ := mem_barSub.mp hxbar
  obtain ⟨o, hoTwo, t, htcen, hC⟩ := hG (x : G) hxA
  have hoK : o ∈ barPre H φ Kb := by
    have hle : oTwoMod C (barPre H φ Kb) ≤ barPre H φ Kb := by
      unfold oTwoMod
      refine iSup_le fun W => iSup_le fun hW => hW.2.1
    exact hle hoTwo
  have hoH : o ∈ H := barPre_le H φ Kb hoK
  have hxH : (x : G) ∈ H := x.2
  have htH : t ∈ H := by
    have hmem : t⁻¹ * o⁻¹ * (x : G) ∈ H := by
      have hC' : (o * t)⁻¹ * (x : G) ∈ C := hC
      have heq : (o * t)⁻¹ * (x : G) = t⁻¹ * o⁻¹ * (x : G) := by group
      rw [heq] at hC'
      exact hCH hC'
    have heq : t⁻¹ = (t⁻¹ * o⁻¹ * (x : G)) * (o⁻¹ * (x : G))⁻¹ := by group
    have htinv : t⁻¹ ∈ H := by
      rw [heq]
      exact H.mul_mem hmem (H.inv_mem (H.mul_mem (H.inv_mem hoH) hxH))
    simpa using H.inv_mem htinv
  refine ⟨φ ⟨o, hoH⟩, ?_, φ ⟨t, htH⟩, ?_, ?_⟩
  · have hmem : o ∈ barPre H φ (oTwoMod (⊥ : Subgroup Q) Kb) := by
      rw [← oTwoMod_barPre hφ hCH Kb]
      exact hoTwo
    obtain ⟨hoH', hoφ⟩ := mem_barPre.mp hmem
    convert hoφ using 2
  · constructor
    · exact mem_barSub.mpr ⟨⟨t, htH⟩, htcen.1, rfl⟩
    · intro lb hlb
      obtain ⟨l, hl⟩ := hφ.surjective lb
      have hlPre : (l : G) ∈ barPre H φ Lb := mem_barPre.mpr ⟨l.2, by rwa [hl]⟩
      have hcomm : t * (l : G) * t⁻¹ * (l : G)⁻¹ ∈ C := htcen.2 (l : G) hlPre
      have hker : φ (⟨t, htH⟩ * l * ⟨t, htH⟩⁻¹ * l⁻¹) = 1 :=
        (hφ.ker_iff _).mpr (by simpa using hcomm)
      rw [← hl]
      simpa [map_mul, map_inv] using hker
  · have hker : φ ((⟨o, hoH⟩ * ⟨t, htH⟩)⁻¹ * x) = 1 :=
      (hφ.ker_iff _).mpr (by simpa using hC)
    rw [Subgroup.mem_bot]
    simpa only [map_mul, map_inv, mul_inv_rev] using hker

private theorem wc813ppull_relIndex_barPre (hφ : IsBarMap H C φ)
    {Ab Bb : Subgroup Q} (hAB : Ab ≤ Bb) :
    (barPre H φ Ab).relIndex (barPre H φ Bb) = Ab.relIndex Bb := by
  simp only [barPre]
  rw [Subgroup.relIndex_map_map_of_injective (f := H.subtype) (H := Ab.comap φ)
    (K := Bb.comap φ) H.subtype_injective]
  rw [Subgroup.relIndex_comap (f := φ) (K := Bb.comap φ)]
  rw [Subgroup.map_comap_eq_self_of_surjective hφ.surjective Bb]

private theorem wc813ppull_barPre_inf_eq (hφ : IsBarMap H C φ) (hCH : C ≤ H)
    {M : Subgroup G} (hCM : C ≤ M) (Kb : Subgroup Q) :
    barPre H φ Kb ⊓ M = barPre H φ (Kb ⊓ barSub H φ (H ⊓ M)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgKb, hgM⟩ := hg
    obtain ⟨hgH, hgφKb⟩ := mem_barPre.mp hgKb
    refine mem_barPre.mpr ⟨hgH, ⟨hgφKb, ?_⟩⟩
    exact mem_barSub.mpr ⟨⟨g, hgH⟩, ⟨hgH, hgM⟩, rfl⟩
  · intro g hg
    obtain ⟨hgH, hgφ⟩ := mem_barPre.mp hg
    obtain ⟨hgφKb, hgφMb⟩ := hgφ
    refine ⟨mem_barPre.mpr ⟨hgH, hgφKb⟩, ?_⟩
    obtain ⟨m, ⟨hmH, hmM⟩, hmφ⟩ := mem_barSub.mp hgφMb
    have hker : φ (⟨g, hgH⟩ * m⁻¹) = 1 := by
      rw [map_mul, map_inv, hmφ]
      group
    have hC : g * (m : G)⁻¹ ∈ C := by
      have := (hφ.ker_iff (⟨g, hgH⟩ * m⁻¹)).mp hker
      simpa using this
    have hg_eq : g = (g * (m : G)⁻¹) * (m : G) := by group
    rw [hg_eq]
    exact M.mul_mem (hCM hC) hmM

theorem d_index_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {M : Subgroup G} (hCM : C ≤ M)
    {Kb : Subgroup Q} (h : (Kb ⊓ barSub H φ (H ⊓ M)).relIndex Kb = 5) :
    (barPre H φ Kb ⊓ M).relIndex (barPre H φ Kb) = 5 := by
  rw [wc813ppull_barPre_inf_eq hφ hCH hCM Kb]
  rw [wc813ppull_relIndex_barPre hφ (inf_le_left : Kb ⊓ barSub H φ (H ⊓ M) ≤ Kb)]
  exact h

theorem barSub_conjClosure_le {L : Subgroup G} (hLH : L ≤ H) :
    barSub H φ (conjClosure L H) ≤ conjClosure (barSub H φ L) ⊤ := by
  have h1 : conjClosure L H ≤ barPre H φ (conjClosure (barSub H φ L) ⊤) := by
    refine conjClosure_le fun h hh z hz => ?_
    have hzh : h * z * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh (hLH hz)) (H.inv_mem hh)
    refine mem_barPre.mpr ⟨hzh, ?_⟩
    have hphi : φ ⟨h * z * h⁻¹, hzh⟩ =
        φ ⟨h, hh⟩ * φ ⟨z, hLH hz⟩ * (φ ⟨h, hh⟩)⁻¹ := by
      rw [show (⟨h * z * h⁻¹, hzh⟩ : ↥H) = ⟨h, hh⟩ * ⟨z, hLH hz⟩ * ⟨h, hh⟩⁻¹
        from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [hphi]
    exact mem_conjClosure (Subgroup.mem_top _) (mem_barSub.mpr ⟨⟨z, hLH hz⟩, hz, rfl⟩)
  calc barSub H φ (conjClosure L H)
      ≤ barSub H φ (barPre H φ (conjClosure (barSub H φ L) ⊤)) :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono H h1)
    _ ≤ conjClosure (barSub H φ L) ⊤ := by
      rw [barSub]
      have hsub : (barPre H φ (conjClosure (barSub H φ L) ⊤)).subgroupOf H =
          (conjClosure (barSub H φ L) ⊤).comap φ := by
        change ((((conjClosure (barSub H φ L) ⊤).comap φ).map H.subtype).subgroupOf H) =
          (conjClosure (barSub H φ L) ⊤).comap φ
        rw [← Subgroup.comap_subtype,
          Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      rw [hsub]
      exact Subgroup.map_comap_le (f := φ) (conjClosure (barSub H φ L) ⊤)

theorem eShape_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {T A : Subgroup G} (hAH : A ≤ H)
    (hTH : T ≤ H) {Lb Kb : Subgroup Q}
    (h : EShape813Gen (⊥ : Subgroup Q) ⊤ (barSub H φ T) (barSub H φ A) Lb Kb) :
    EShape813Gen C H T A (barPre H φ Lb) (barPre H φ Kb) := by
  rcases h with (hL2 | hU3) | ⟨hRank, hPar | hCent⟩
  · left; left
    have := hasQuotShape_barPre hφ hL2
    rwa [barPre_bot hφ hCH] at this
  · left; right
    have := hasQuotShape_barPre hφ hU3
    rwa [barPre_bot hφ hCH] at this
  · have hRankC : ShapeRankTwoMod C (barPre H φ Lb) := by
      rcases hRank with hL3 | hSL3 | hSp4
      · left; have := hasQuotShape_barPre hφ hL3; rwa [barPre_bot hφ hCH] at this
      · right; left; have := hasQuotShape_barPre hφ hSL3
        rwa [barPre_bot hφ hCH] at this
      · right; right; have := hasQuotShape_barPre hφ hSp4
        rwa [barPre_bot hφ hCH] at this
    obtain ⟨P, hP, hK⟩ := hPar
    exact Or.inr ⟨hRankC, Or.inl ⟨barPre H φ P, isMaxParabolicMod_barPre hφ hCH hP,
      by rw [hK, oddResMod_barPre hφ hCH P]⟩⟩
  · have hRankC : ShapeRankTwoMod C (barPre H φ Lb) := by
      rcases hRank with hL3 | hSL3 | hSp4
      · left; have := hasQuotShape_barPre hφ hL3; rwa [barPre_bot hφ hCH] at this
      · right; left; have := hasQuotShape_barPre hφ hSL3
        rwa [barPre_bot hφ hCH] at this
      · right; right; have := hasQuotShape_barPre hφ hSp4
        rwa [barPre_bot hφ hCH] at this
    refine Or.inr ⟨hRankC, Or.inr ?_⟩
    intro a ha t ht
    have haH : a ∈ H := hAH ha
    have htT : t ∈ T := ht.1
    have htH : t ∈ H := hTH htT
    have hbarA : φ ⟨a, haH⟩ ∈ barSub H φ A := mem_barSub.mpr ⟨⟨a, haH⟩, ha, rfl⟩
    have hbarT : φ ⟨t, htH⟩ ∈ barSub H φ T := mem_barSub.mpr ⟨⟨t, htH⟩, htT, rfl⟩
    have hbarClosure : φ ⟨t, htH⟩ ∈ conjClosure Lb ⊤ := by
      have h1 : φ ⟨t, htH⟩ ∈ barSub H φ (conjClosure (barPre H φ Lb) H) :=
        mem_barSub.mpr ⟨⟨t, htH⟩, ht.2, rfl⟩
      have h2 := barSub_conjClosure_le (φ := φ) (H := H) (barPre_le H φ Lb) h1
      rwa [barSub_barPre hφ Lb] at h2
    have hcomm := hCent (φ ⟨a, haH⟩) hbarA (φ ⟨t, htH⟩) ⟨hbarT, hbarClosure⟩
    rw [Subgroup.mem_bot] at hcomm
    exact (hφ.ker_iff (⟨a, haH⟩ * ⟨t, htH⟩ * ⟨a, haH⟩⁻¹ * ⟨t, htH⟩⁻¹)).mp (by
      simp only [map_mul, map_inv]
      exact hcomm)

private theorem wc813ppull_relIndex_sup_eq (hCH : C ≤ H) {S : Subgroup G} (hSH : S ≤ H)
    (hCnorm : (C.subgroupOf H).Normal) :
    S.relIndex (S ⊔ C) = (S ⊓ C).relIndex C := by
  have hC_le : C ≤ S ⊔ C := le_sup_right
  have hSC_le : S ⊓ C ≤ C := inf_le_right
  have h1 := Subgroup.relIndex_inf_mul_relIndex (H := C) (K := S) (L := S ⊔ C)
  rw [inf_of_le_left le_sup_left, inf_comm] at h1
  have h2 := Subgroup.relIndex_mul_relIndex (H := S ⊓ C) (K := C) (L := S ⊔ C)
    hSC_le hC_le
  have h3 : C.relIndex (S ⊔ C) = C.relIndex S := by
    have hsup : S ⊔ C ≤ H := sup_le hSH hCH
    have h5 := Subgroup.relIndex_sup_right (H := S.subgroupOf H) (K := C.subgroupOf H)
    rw [← Subgroup.subgroupOf_sup hSH hCH] at h5
    rw [Subgroup.relIndex_subgroupOf (H := C) (K := S ⊔ C) (L := H) hsup,
        Subgroup.relIndex_subgroupOf (H := C) (K := S) (L := H) hSH] at h5
    exact h5
  rw [h3] at h2
  rw [← h2] at h1
  have hpos : 0 < C.relIndex S := by
    rw [Subgroup.relIndex]
    exact Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm]; exact h1)

theorem isSylowIn_inf_barPre (hφ : IsBarMap H C φ) (hCH : C ≤ H) {T : Subgroup G}
    (hT : IsSylowIn 2 T H) {Kb : Subgroup Q}
    (h : IsSylowIn 2 (barSub H φ T ⊓ Kb) Kb) :
    IsSylowIn 2 (T ⊓ barPre H φ Kb) (barPre H φ Kb) := by
  have hCnorm : (C.subgroupOf H).Normal := by
    have hker : C.subgroupOf H = φ.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact (hφ.ker_iff x).symm
    rw [hker]
    exact MonoidHom.normal_ker φ
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_subgroupOf_normal hCH hCnorm
  have hS'_eq : T ⊓ barPre H φ Kb ⊔ C =
      barPre H φ (barSub H φ T ⊓ Kb) := by
    apply le_antisymm
    · refine sup_le ?_ (le_barPre hCH hφ _)
      intro g hg
      obtain ⟨hgT, hgK⟩ := hg
      have hgH : g ∈ H := barPre_le H φ Kb hgK
      refine mem_barPre.mpr ⟨hgH, ⟨?_, ?_⟩⟩
      · exact mem_barSub.mpr ⟨⟨g, hgH⟩, hgT, rfl⟩
      · exact (mem_barPre.mp hgK).2
    · intro g hg
      obtain ⟨hgH, hgTb, hgKb⟩ := mem_barPre.mp hg
      have hgK : g ∈ barPre H φ Kb := mem_barPre.mpr ⟨hgH, hgKb⟩
      obtain ⟨t, htT, htφ⟩ := mem_barSub.mp hgTb
      have htK : (t : G) ∈ barPre H φ Kb := mem_barPre.mpr ⟨t.2, by rwa [htφ]⟩
      have htS : (t : G) ∈ T ⊓ barPre H φ Kb := ⟨htT, htK⟩
      have hker : φ (⟨g, hgH⟩ * t⁻¹) = 1 := by
        rw [map_mul, map_inv, htφ]
        group
      have hCg : g * (t : G)⁻¹ ∈ C := (hφ.ker_iff (⟨g, hgH⟩ * t⁻¹)).mp hker
      have hg_eq : g = (g * (t : G)⁻¹) * (t : G) := by group
      rw [hg_eq]
      exact (T ⊓ barPre H φ Kb ⊔ C).mul_mem (Subgroup.mem_sup_right hCg)
        (Subgroup.mem_sup_left htS)
  have hodd1 : Odd ((T ⊓ barPre H φ Kb).relIndex (barPre H φ (barSub H φ T ⊓ Kb))) := by
    rw [← hS'_eq]
    rw [wc813ppull_relIndex_sup_eq hCH (inf_le_right.trans (barPre_le H φ Kb)) hCnorm]
    have hCS : T ⊓ barPre H φ Kb ⊓ C = T ⊓ C := by
      ext x; constructor
      · intro hx; exact ⟨hx.1.1, hx.2⟩
      · intro hx; exact ⟨⟨hx.1, le_barPre hCH hφ Kb hx.2⟩, hx.2⟩
    rw [hCS]
    exact Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp (hT.inf_normal hCH hCnorm).2.2)
  have hodd2 : Odd ((barPre H φ (barSub H φ T ⊓ Kb)).relIndex (barPre H φ Kb)) := by
    rw [wc813ppull_relIndex_barPre hφ (inf_le_right : barSub H φ T ⊓ Kb ≤ Kb)]
    exact Nat.not_even_iff_odd.mp (mt even_iff_two_dvd.mp h.2.2)
  have hSS' : T ⊓ barPre H φ Kb ≤ barPre H φ (barSub H φ T ⊓ Kb) := by
    rw [← hS'_eq]
    exact le_sup_left
  have hS'K : barPre H φ (barSub H φ T ⊓ Kb) ≤ barPre H φ Kb := by
    rw [← hS'_eq]
    exact sup_le inf_le_right (le_barPre hCH hφ Kb)
  have hmul := Subgroup.relIndex_mul_relIndex
    (H := T ⊓ barPre H φ Kb) (K := barPre H φ (barSub H φ T ⊓ Kb))
    (L := barPre H φ Kb) hSS' hS'K
  have hodd3 : Odd ((T ⊓ barPre H φ Kb).relIndex (barPre H φ Kb)) := by
    rw [← hmul]
    exact hodd1.mul hodd2
  exact ⟨inf_le_right, IsPGroup.to_le hT.2.1 inf_le_left,
    mt even_iff_two_dvd.mpr (Nat.not_even_iff_odd.mpr hodd3)⟩

theorem Concl813Gen.of_bar (hφ : IsBarMap H C φ) (hCH : C ≤ H) {M T A : Subgroup G}
    (hCM : C ≤ M) (hT : IsSylowIn 2 T H) (hAH : A ≤ H) {Lb Kb : Subgroup Q}
    (h : Concl813Gen (⊥ : Subgroup Q) (barSub H φ (H ⊓ M)) ⊤ (barSub H φ T)
      (barSub H φ A) Lb Kb) :
    Concl813Gen C M H T A (barPre H φ Lb) (barPre H φ Kb) where
  comp := isComponentModN_barPre hφ hCH h.comp
  sub_L := fun g hg => mem_barPre.mpr ⟨(mem_barPre.mp hg).1, h.sub_L (mem_barPre.mp hg).2⟩
  ge_C := le_barPre hCH hφ Kb
  a_le := a_le_barPre hφ hCH hAH h.a_le
  b_not_le := b_not_le_barPre hφ hCH hAH h.b_not_le
  c_shape := by
    rw [oTwoMod_barPre hφ hCH Kb]
    exact hasQuotShape_barPre hφ h.c_shape
  d_index := d_index_barPre hφ hCH hCM h.d_index
  e_shape := eShape_barPre hφ hCH hAH hT.1 h.e_shape
  t_sylow := isSylowIn_inf_barPre hφ hCH hT h.t_sylow

theorem Concl813''.of_bar {V H T A : Subgroup G} {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) (hCH : cGrp H T ≤ H)
    (hCM : cGrp H T ≤ normalizer (V : Set G)) (hT : IsSylowIn 2 T H) (hAH : A ≤ H)
    {Lb Kb : Subgroup Q}
    (h : Concl813Gen (⊥ : Subgroup Q) (barSub H φ (H ⊓ normalizer (V : Set G))) ⊤
      (barSub H φ T) (barSub H φ A) Lb Kb) :
    Concl813'' V H T A (barPre H φ Lb) (barPre H φ Kb) :=
  Concl813Gen.of_bar hφ hCH hCM hT hAH h

end Pull

end CFSG.LocalAnalysis.WeakClosure81

end
