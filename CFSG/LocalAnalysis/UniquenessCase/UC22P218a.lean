module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_inner rhoL_fix_iff normalizer_le_normalizer_pCoreOf)

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_rhoL_eq {L T : Subgroup G} (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G))
    (hS : IsSylowOf 2 (T ⊓ L) L)
    (hinn : (T.subgroupOf (normalizer (L : Set G))).map (rhoL L) ≤
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range)
    {t : G} (ht : t ∈ T) :
    ∃ s : G, ∃ hs : s ∈ T ⊓ L, rhoL L ⟨s, le_normalizer (mem_inf.1 hs).2⟩ = rhoL L ⟨t, hTL ht⟩ := by
  obtain ⟨Q, hQ⟩ := hS
  have hQT : ∀ q : ↥L, q ∈ (Q : Subgroup ↥L) → (q : G) ∈ T ⊓ L := fun q hq => by
    rw [← hQ]
    exact mem_map_of_mem _ hq
  obtain ⟨ψ, hψ, hψr⟩ : ∃ ψ : ↥L →* MulAut (Bar2 L), (∀ l : ↥L, ψ l = rhoL L ⟨l, le_normalizer l.2⟩) ∧
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range ≤ ψ.range := by
    refine ⟨(MulAut.conj : Bar2 L →* MulAut (Bar2 L)).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
      fun l => (rhoL_inner L l l.2).symm, ?_⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
    exact ⟨l, rfl⟩
  have hQR : (Q : Subgroup ↥L).map ψ ≤ (T.subgroupOf (normalizer (L : Set G))).map (rhoL L) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hψ]
    exact mem_map_of_mem _ (mem_subgroupOf.2 (mem_inf.1 (hQT q hq)).1)
  have hRp : IsPGroup 2 (((T.subgroupOf (normalizer (L : Set G))).map (rhoL L)).subgroupOf ψ.range) :=
    ((hT.comap_subtype (K := normalizer (L : Set G))).map (rhoL L)).comap_subtype
  let Sb : Sylow 2 ↥ψ.range := Q.mapSurjective ψ.rangeRestrict_surjective
  have hle : (Sb : Subgroup ↥ψ.range) ≤
      ((T.subgroupOf (normalizer (L : Set G))).map (rhoL L)).subgroupOf ψ.range := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := (ha : a ∈ (Q : Subgroup ↥L).map ψ.rangeRestrict)
    rw [mem_subgroupOf, MonoidHom.coe_rangeRestrict]
    exact hQR (mem_map_of_mem ψ hq)
  have heq := Sb.is_maximal' hRp hle
  have htN : (⟨t, hTL ht⟩ : ↥(normalizer (L : Set G))) ∈ T.subgroupOf (normalizer (L : Set G)) :=
    mem_subgroupOf.2 ht
  have htR : rhoL L ⟨t, hTL ht⟩ ∈ (T.subgroupOf (normalizer (L : Set G))).map (rhoL L) := mem_map_of_mem _ htN
  have htS : (⟨rhoL L ⟨t, hTL ht⟩, hinn.trans hψr htR⟩ : ↥ψ.range) ∈ (Sb : Subgroup ↥ψ.range) := by
    rw [← heq, mem_subgroupOf]
    exact htR
  obtain ⟨q, hq, hqt⟩ := (htS : _ ∈ (Q : Subgroup ↥L).map ψ.rangeRestrict)
  refine ⟨q, hQT q hq, ?_⟩
  rw [← hψ q]
  exact congrArg Subtype.val hqt

theorem conj_mem_of_rhoL_eq {L T : Subgroup G} (hO : pCoreOf 2 L ≤ T) {s t x : G} (hsT : s ∈ T ⊓ L)
    (ht : t ∈ T) (htL : t ∈ normalizer (L : Set G))
    (hst : rhoL L ⟨s, le_normalizer (mem_inf.1 hsT).2⟩ = rhoL L ⟨t, htL⟩)
    (hx : x ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G)) : x * t * x⁻¹ ∈ T := by
  obtain ⟨hxL, hxN⟩ := mem_inf.1 hx
  have hcN : s⁻¹ * t ∈ normalizer (L : Set G) := mul_mem (inv_mem (le_normalizer (mem_inf.1 hsT).2)) htL
  have hc1 : rhoL L ⟨s⁻¹ * t, hcN⟩ = 1 := by
    have : (⟨s⁻¹ * t, hcN⟩ : ↥(normalizer (L : Set G))) =
        (⟨s, le_normalizer (mem_inf.1 hsT).2⟩ : ↥(normalizer (L : Set G)))⁻¹ * ⟨t, htL⟩ := rfl
    rw [this, map_mul, map_inv, hst, inv_mul_cancel]
  have hfix : s⁻¹ * t * x⁻¹ * (s⁻¹ * t)⁻¹ * x⁻¹⁻¹ ∈ pCoreOf 2 L :=
    (rhoL_fix_iff L ⟨s⁻¹ * t, hcN⟩ ⟨x⁻¹, inv_mem hxL⟩).1 (by simp [hc1])
  have hxO : x ∈ normalizer (pCoreOf 2 L : Set G) := normalizer_le_normalizer_pCoreOf L (le_normalizer hxL)
  have h1 : x * (s⁻¹ * t * x⁻¹ * (s⁻¹ * t)⁻¹ * x⁻¹⁻¹) * x⁻¹ ∈ pCoreOf 2 L :=
    (mem_normalizer_iff.1 hxO _).1 hfix
  have h2 : x * s * x⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.1 hxN s).1 hsT
  have hcT : s⁻¹ * t ∈ T := mul_mem (inv_mem (mem_inf.1 hsT).1) ht
  have key : x * t * x⁻¹ =
      x * s * x⁻¹ * (x * (s⁻¹ * t * x⁻¹ * (s⁻¹ * t)⁻¹ * x⁻¹⁻¹) * x⁻¹) * (s⁻¹ * t) := by
    group
  rw [key]
  exact mul_mem (mul_mem (mem_inf.1 h2).1 (hO h1)) hcT

theorem inf_normalizer_le_normalizer_of_inner {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L)
    (hinn : (T.subgroupOf (normalizer (L : Set G))).map (rhoL L) ≤
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range) :
    L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ normalizer (T : Set G) := by
  have hO : pCoreOf 2 L ≤ T := by
    obtain ⟨Q, hQ⟩ := hS
    have h : (CFSG.pCore 2 ↥L).map L.subtype ≤ T ⊓ L := by
      rw [← hQ]
      exact map_mono (CFSG.fitting_pCore_le_sylow Q)
    exact h.trans inf_le_left
  have key : ∀ x ∈ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G), ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
    intro x hx t ht
    obtain ⟨s, hs, hst⟩ := exists_mem_inf_rhoL_eq hT hTL hS hinn ht
    exact conj_mem_of_rhoL_eq hO hs ht (hTL ht) hst hx
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  refine ⟨key x hx h, fun hh => ?_⟩
  have hx' := key x⁻¹ (inv_mem hx) (x * h * x⁻¹) hh
  have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
  rwa [e] at hx'

theorem exists_not_inner_of_not_le_normalizer {L T X : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hS : IsSylowOf 2 (T ⊓ L) L)
    (hX : X ≤ L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G)) (hXT : ¬ X ≤ normalizer (T : Set G)) :
    ∃ t : G, ∃ ht : t ∈ T, rhoL L ⟨t, hTL ht⟩ ∉ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := by
  by_contra hno
  push_neg at hno
  refine hXT (hX.trans (inf_normalizer_le_normalizer_of_inner hT hTL hS ?_))
  rintro _ ⟨⟨t, htN⟩, ht, rfl⟩
  exact hno t (mem_subgroupOf.1 ht)

end CFSG.LocalAnalysis.UniquenessCase.UC22
