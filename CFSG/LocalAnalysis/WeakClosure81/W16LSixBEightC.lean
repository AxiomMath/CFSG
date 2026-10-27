module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBEightB
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBM

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16l_conj_img_eq (D : ModDataE H (iSub16 V H)) (hVH : V ≤ H) {j : ↥H} :
    conjSubgroup (D.img V) (D.ρ j) = D.img (conjSubgroup V (j : G)) := by
  have h := D.img_conj hVH (j⁻¹)
  rw [map_inv, Subgroup.coe_inv, inv_inv] at h
  exact h

private theorem w16l_map_top_projG (D : ModDataE H (iSub16 V H)) :
    (⊤ : Subgroup (VG (D.img H))).map (projG (D.img H)) = D.img H := by
  rw [← MonoidHom.range_eq_map]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨v, g', rfl⟩ := exists_eq_inl_mul_inr y
    rw [map_mul, projG_inl, one_mul, projG_inr]
    exact g'.2
  · intro hx
    exact ⟨SemidirectProduct.inr ⟨x, hx⟩, by rw [projG_inr]⟩

theorem IsMinFam16.not_hat_le_normalizer (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ¬ D.img H ≤ Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hV_le_L : D.img V ≤ D.img H := D.img_mono hVH
  have hV_mem_Gamma : D.img V ∈ hatGamma D V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hass := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  let L : Subgroup (LGL 2 D.W) := D.img H
  let φ : ↥H →* ↥L := D.ρ.codRestrict L fun j => D.mem_img.2 ⟨j, j.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨j, _hj, hjx⟩ := D.mem_img.1 x.2
    exact ⟨j, Subtype.ext hjx⟩
  let A : Subgroup ↥L := (D.img V).subgroupOf L
  have hA_ne_bot : A ≠ ⊥ := by
    intro hbot
    apply hass.ne_bot (D.img V) hV_mem_Gamma
    rw [eq_bot_iff]
    intro y hy
    have hyL : y ∈ L := hV_le_L hy
    have hmem : (⟨y, hyL⟩ : ↥L) ∈ A := hy
    rw [hbot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hAcore : A ⊓ CFSG.pCore 2 ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : LGL 2 D.W) ∈ D.img V ⊓ pCoreOf 2 (D.img H) :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, (CFSG.mem_openPCoreOf_iff x).mpr hx.2⟩
    rw [hass.inf_pCore (D.img V) hV_mem_Gamma] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
  have hW : IsPGroup 2 A := by
    have hV2 : IsPGroup 2 (D.img V) := D.isPGroup_img h.hyp.h6.elemAbelian.isPGroup
    exact hV2.comap_subtype (K := L)
  have hS_norm : (S.subgroupOf H).map φ ≤ Subgroup.normalizer (A : Set ↥L) := by
    rintro x ⟨j, hj, rfl⟩
    have hjS : (j : G) ∈ S := Subgroup.mem_subgroupOf.mp hj
    have hjn : (j : G) ∈ Subgroup.normalizer (V : Set G) := by
      rw [h.hyp.h6.normalizer_eq]
      exact h.S_le_M hjS
    have hconjV : conjSubgroup V ((j : G)⁻¹) = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr ((Subgroup.normalizer (V : Set G)).inv_mem hjn)
    have hnormV : D.ρ j ∈ Subgroup.normalizer
        ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      change cj (D.ρ j) (D.img V) = D.img V
      rw [D.img_conj hVH j, hconjV]
    rw [← Subgroup.subgroupOf_normalizer_eq hV_le_L, Subgroup.mem_subgroupOf]
    exact hnormV
  intro hle
  apply hH.1.2.2
  intro x hxH
  have hPre := w16l_normalizer_preimage_le hH φ hφ A A hA_ne_bot le_rfl hAcore hW hS_norm
  have hxA : φ ⟨x, hxH⟩ ∈ Subgroup.normalizer (A : Set ↥L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hV_le_L, Subgroup.mem_subgroupOf]
    exact hle ((D.mem_img (S := H)).2 ⟨⟨x, hxH⟩, hxH, rfl⟩)
  exact Subgroup.mem_subgroupOf.mp (hPre (Subgroup.mem_comap.mpr hxA))

section Certified


theorem IsMinFam16.map_projG_wClos_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    (E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S)).map (projG (D.img H)) = hatW0 D V S := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hA₁ : IsElemAbelian 2 (hatV1 D V₀ V) :=
    (IsMinFam16.hyp711_img h1 h5 hS h hH hV D).elemAbelian
  let A₁ : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  let π : VG (D.img H) →* LGL 2 D.W := projG (D.img H)
  have hA₁map : A₁.map π = D.img V :=
    map_projG_wHat_sup_aHat (W := hatVA D V₀ V (D.img V)) (A := D.img V) (D.img_mono hVH)
  have hT : hatT1 D S = (D.img S).comap π := rfl
  have key : (⨆ g : VG (D.img H), ⨆ (_ : conjSubgroup A₁ g ≤ hatT1 D S),
        conjSubgroup (D.img V) (π g)) = hatW0 D V S := by
    refine le_antisymm ?_ ?_
    · unfold hatW0
      refine iSup₂_le fun g hg => ?_
      have hmap_le : conjSubgroup (D.img V) (π g) ≤ D.img S := by
        rw [← hA₁map, map_conjSubgroup_hom π A₁ g]
        exact Subgroup.map_le_iff_le_comap.mpr (by rwa [hT] at hg)
      have hπg : π g ∈ D.img H := by
        obtain ⟨v, g', rfl⟩ := exists_eq_inl_mul_inr g
        rw [map_mul, projG_inl, one_mul, projG_inr]
        exact g'.2
      obtain ⟨j, hj⟩ := D.mem_img.1 hπg
      have hBmem : conjSubgroup (D.img V) (π g) ∈ hatGamma D V :=
        ⟨j, j.2, by rw [← hj.2]; exact w16l_conj_img_eq D hVH⟩
      exact le_iSup_of_le (conjSubgroup (D.img V) (π g))
        (le_iSup_of_le ⟨hBmem, hmap_le⟩ le_rfl)
    · unfold hatW0
      refine iSup₂_le fun B hB => ?_
      obtain ⟨h', hh', hBeq⟩ := hB.1
      let j : ↥H := ⟨h', hh'⟩
      let g : VG (D.img H) :=
        SemidirectProduct.inr (⟨D.ρ j, D.mem_img.2 ⟨j, hh', rfl⟩⟩ : D.img H)
      have hπg : π g = D.ρ j := by
        simp only [g, π, projG_inr]
      have hBeq' : B = D.img (conjSubgroup V (j : G)) := hBeq
      have hgT : conjSubgroup A₁ g ≤ hatT1 D S := by
        rw [hT, ← Subgroup.map_le_iff_le_comap]
        rw [← map_conjSubgroup_hom π A₁ g, hA₁map, hπg, w16l_conj_img_eq D hVH]
        exact hBeq ▸ hB.2
      rw [hBeq', ← w16l_conj_img_eq D hVH, ← hπg]
      exact le_iSup₂_of_le g hgT le_rfl
  calc (E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S)).map (projG (D.img H))
      = (E3.wClos A₁ 0 (hatT1 D S)).map π := rfl
    _ = (⨆ g : VG (D.img H), ⨆ (_ : conjSubgroup A₁ g ≤ hatT1 D S),
          conjSubgroup A₁ g).map π := by rw [wClos_zero_eq_iSup hA₁]
    _ = ⨆ g : VG (D.img H), ⨆ (_ : conjSubgroup A₁ g ≤ hatT1 D S),
          (conjSubgroup A₁ g).map π := by
        rw [Subgroup.map_iSup]; simp_rw [Subgroup.map_iSup]
    _ = ⨆ g : VG (D.img H), ⨆ (_ : conjSubgroup A₁ g ≤ hatT1 D S),
          conjSubgroup (D.img V) (π g) := by
        refine iSup_congr fun g => iSup_congr fun _ => ?_
        rw [← map_conjSubgroup_hom π A₁ g, hA₁map]
    _ = hatW0 D V S := key

theorem IsMinFam16.not_hyp85Three_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) (hF : W3Lem85ThreeFirst' (VG (D.img H))) :
    ¬ Hyp85Three' (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (hatT1 D S) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hA₁map : (hatV1 D V₀ V).map (projG (D.img H)) = D.img V :=
    map_projG_wHat_sup_aHat (W := hatVA D V₀ V (D.img V)) (A := D.img V) (D.img_mono hVH)
  have h83 := IsMinFam16.hyp83_hat h1 h5 hS h hH hV D
  have htop := IsMinFam16.top_eq_kGenIn_sup_hatT1 h1 h5 hS h hH hV D
  let π : VG (D.img H) →* LGL 2 D.W := projG (D.img H)
  have hrange : (⊤ : Subgroup (VG (D.img H))).map π = D.img H :=
    w16l_map_top_projG D
  intro hyp
  have hmain := hF (hatV1 D V₀ V) ⊤ (hatT1 D S)
    ⟨h83.elemAbelian, h83.two_lt_card, h83.isTI⟩ h83.isCalH h83.not_isCalH0
    h83.sylow htop hyp
  have htopπ : D.img H =
      ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
        ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H)))).map π ⊔
      ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
        ((E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S) : Subgroup (VG (D.img H))) :
          Set (VG (D.img H)))).map π := by
    have h := congrArg (Subgroup.map π) hmain
    rw [Subgroup.map_sup] at h
    rwa [hrange] at h
  have hX : ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
      ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H)))).map π ≤
      Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
    calc ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
          ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H)))).map π
        ≤ (Subgroup.normalizer ((hatV1 D V₀ V : Subgroup (VG (D.img H))) :
            Set (VG (D.img H)))).map π := Subgroup.map_mono inf_le_right
      _ ≤ Subgroup.normalizer (((hatV1 D V₀ V).map π : Subgroup (LGL 2 D.W)) :
            Set (LGL 2 D.W)) := Subgroup.le_normalizer_map π
      _ = Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
            rw [hA₁map]
  have hY : ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
      ((E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S) : Subgroup (VG (D.img H))) :
        Set (VG (D.img H)))).map π ≤
      Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
    have hY1 : ((⊤ : Subgroup (VG (D.img H))) ⊓ Subgroup.normalizer
        ((E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S) : Subgroup (VG (D.img H))) :
          Set (VG (D.img H)))).map π ≤ Subgroup.normalizer
        (((E3.wClos (hatV1 D V₀ V) 0 (hatT1 D S)).map π : Subgroup (LGL 2 D.W)) :
          Set (LGL 2 D.W)) :=
      (Subgroup.map_mono inf_le_right).trans (Subgroup.le_normalizer_map π)
    rw [IsMinFam16.map_projG_wClos_hat h1 h5 hS h hH hV D] at hY1
    intro n hn
    have hnH : n ∈ D.img H := by
      have := Subgroup.map_mono inf_le_left hn
      rwa [hrange] at this
    exact IsMinFam16.hat_normalizer_W0_le h1 h5 hS h hH hV D n hnH (hY1 hn)
  exact IsMinFam16.not_hat_le_normalizer h1 h5 hS h hH hV D (by
    rw [htopπ]
    exact sup_le hX hY)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
