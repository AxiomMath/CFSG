module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixSeven
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3Hyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

@[expose] def hatT1 (D : ModDataE H (iSub16 V H)) (S : Subgroup G) : Subgroup (VG (D.img H)) :=
  (D.img S).comap (projG (D.img H))

private theorem w16l_projG_range (D : ModDataE H (iSub16 V H)) :
    (projG (D.img H)).range = D.img H := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2.2
  · intro hg
    exact ⟨SemidirectProduct.inr ⟨g, hg⟩, rfl⟩

private theorem w16l_commSub_img_V_le_sp_V₀ (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    commSub (D.img V) ≤ D.sp V₀ := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hI_le_S : iSub16 V H ≤ S :=
    (Cex16.iSub16_le_pCoreOf h hH.1).trans (h.pCoreOf_le_S h1 hS hH.1)
  have hcommIV : ⁅iSub16 V H, V⁆ ≤ V₀ :=
    Subgroup.commutator_le.mpr fun i hi v hv => h.comm_mem_V₀ (hI_le_S hi) hv
  calc commSub (D.img V) = D.sp ⁅iSub16 V H, V⁆ := by
        refine le_antisymm ?_ ?_
        · intro w hw
          obtain ⟨e, he, rfl⟩ := D.ι_surj w
          exact D.mem_sp.2 ⟨e, ⟨(D.mem_commSub_img_iff hVH he).1 hw, he⟩, rfl⟩
        · intro w hw
          obtain ⟨e, he, rfl⟩ := D.mem_sp.1 hw
          exact (D.mem_commSub_img_iff hVH he.2).2 he.1
    _ ≤ D.sp V₀ := D.sp_mono hcommIV

section Certified


theorem IsMinFam16.hatT1_sylow (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H)
    (D : ModDataE H (iSub16 V H)) :
    IsSylowIn 2 (hatT1 D S) (⊤ : Subgroup (VG (D.img H))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker2 : IsPGroup 2 (projG (D.img H)).ker :=
    (isElemAbelian_wHat (G := D.img H) ⊤).isPGroup.to_le
      (ker_projG_le_vHat (V := D.W))
  have hT2 : IsPGroup 2 (hatT1 D S) := by
    rw [hatT1]
    exact (D.isPGroup_img h.sylow.isPGroup).comap_of_ker_isPGroup
      (projG (D.img H)) hker2
  have hSH : IsSylowIn 2 S H := h.isSylowIn_of_fam h1 hS hH.1
  have hSHat : IsSylowIn 2 (D.img S) (D.img H) := D.isSylowIn_img_of_isSylowIn hSH
  refine ⟨le_top, hT2, ?_⟩
  have hrel : (hatT1 D S).relIndex (⊤ : Subgroup (VG (D.img H))) =
      (D.img S).relIndex (D.img H) := by
    rw [hatT1, Subgroup.relIndex_comap, Subgroup.map_top, w16l_projG_range D]
  rw [hrel]
  exact hSHat.not_dvd_relIndex

theorem IsMinFam16.hatT1_le_normalizer (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    hatT1 D S ≤ Subgroup.normalizer
      ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H))) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hVA : hatVA D V₀ V (D.img V) = D.sp V₀ :=
    Cex16.conjImgSpace_img_eq h1 h5 hS h hH.1 hV D
  have hcomm_sub : commSub (D.img V) ≤ D.sp V₀ :=
    w16l_commSub_img_V_le_sp_V₀ h1 hS h hH hV D
  have hVnorm : vHat (D.img H) ≤ Subgroup.normalizer
      ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H))) := by
    have h := vHat_le_normalizer_wHat_sup_aHat (G := D.img H)
      (W := hatVA D V₀ V (D.img V)) (A := D.img V) (by rw [hVA]; exact hcomm_sub)
    simpa [hatV1, UAOf] using h
  have hS_le_NV : S ≤ Subgroup.normalizer (V : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
  have hS_le_NV0 : S ≤ Subgroup.normalizer (V₀ : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.normalizer₀.symm)
  intro x hx
  obtain ⟨v, g, rfl⟩ := exists_eq_inl_mul_inr x
  have hgS : (g : LGL 2 D.W) ∈ D.img S := by
    have hx' := hx
    rw [hatT1, Subgroup.mem_comap] at hx'
    simpa using hx'
  obtain ⟨j, hjS, hρj⟩ := D.mem_img.1 hgS
  have hgW : conjSub (g : LGL 2 D.W) (hatVA D V₀ V (D.img V)) =
      hatVA D V₀ V (D.img V) := by
    rw [hVA, ← hρj, D.conjSub_sp V₀ j]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (V₀ : Set G)).inv_mem (hS_le_NV0 hjS))
  have hgA : cj (g : LGL 2 D.W) (D.img V) = D.img V := by
    rw [← hρj, D.img_conj hVH j]
    congr 1
    exact conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (V : Set G)).inv_mem (hS_le_NV hjS))
  have hconjA : conjSubgroup (hatV1 D V₀ V)
      (SemidirectProduct.inr g⁻¹ : VG (D.img H)) = hatV1 D V₀ V := by
    have h := conjSubgroup_wHat_sup_aHat_inr_inv (G := D.img H)
      (W := hatVA D V₀ V (D.img V)) (A := D.img V) g
    rw [hgW, hgA] at h
    simpa [hatV1, UAOf] using h
  have hgN : (SemidirectProduct.inr g : VG (D.img H)) ∈
      Subgroup.normalizer ((hatV1 D V₀ V : Subgroup (VG (D.img H))) :
        Set (VG (D.img H))) := by
    have h1 : (SemidirectProduct.inr g⁻¹ : VG (D.img H)) ∈
        Subgroup.normalizer ((hatV1 D V₀ V : Subgroup (VG (D.img H))) :
          Set (VG (D.img H))) :=
      conjSubgroup_eq_iff_mem_normalizer.mp hconjA
    have h2 := (Subgroup.normalizer _).inv_mem h1
    simpa using h2
  have hvN : (SemidirectProduct.inl (Multiplicative.ofAdd v) : VG (D.img H)) ∈
      Subgroup.normalizer ((hatV1 D V₀ V : Subgroup (VG (D.img H))) :
        Set (VG (D.img H))) :=
    hVnorm (mem_wHat.mpr ⟨v, Submodule.mem_top, rfl⟩)
  exact (Subgroup.normalizer _).mul_mem hvN hgN

theorem IsMinFam16.charTwo_hat (D : ModDataE H (iSub16 V H)) :
    CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup (VG (D.img H))) :=
  charTwo_top_VG (V := D.W) (G := D.img H)

theorem IsMinFam16.not_hatV1_le_pCoreOf (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ¬ hatV1 D V₀ V ≤ pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) := by
  intro hle
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hass : Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hΓ : D.img V ∈ D.conjImgFam V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hmap : (hatV1 D V₀ V).map (projG (D.img H)) = D.img V := by
    show (UAOf (D.img H) (hatVA D V₀ V) (D.img V)).map (projG (D.img H)) = D.img V
    rw [UAOf, map_projG_wHat_sup_aHat (D.img_mono hVH)]
  have hle' : D.img V ≤ pCoreOf 2 (D.img H) := by
    rw [← hmap]
    exact (Subgroup.map_mono hle).trans (map_projG_pCoreOf_le (G := D.img H) (V := D.W))
  have hbot : D.img V ⊓ pCoreOf 2 (D.img H) = ⊥ := hass.inf_pCore (D.img V) hΓ
  have hlebot : D.img V ≤ ⊥ := by
    rw [← hbot]
    exact le_inf le_rfl hle'
  exact hass.ne_bot (D.img V) hΓ (le_antisymm hlebot bot_le)

theorem IsMinFam16.hyp83_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    Hyp83 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (hatT1 D S) := by
  have h711 : SevenK.Hyp711 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))
      (vHat (D.img H)) := IsMinFam16.hyp711_img h1 h5 hS h hH hV D
  have hsy := IsMinFam16.hatT1_sylow h1 hS h hH D
  have hnorm := IsMinFam16.hatT1_le_normalizer h1 h5 hS h hH hV D
  have hchar : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup (VG (D.img H))) :=
    IsMinFam16.charTwo_hat D
  have hnot := IsMinFam16.not_hatV1_le_pCoreOf h1 h5 hS h hH hV D
  let N : Subgroup (VG (D.img H)) := Subgroup.normalizer
    ((hatV1 D V₀ V : Subgroup (VG (D.img H))) : Set (VG (D.img H)))
  have hTle : hatT1 D S ≤ (⊤ : Subgroup (VG (D.img H))) ⊓ N := le_inf le_top hnorm
  have hoddT : Odd ((hatT1 D S).relIndex (⊤ : Subgroup (VG (D.img H)))) :=
    Nat.not_even_iff_odd.mp fun he => hsy.not_dvd_relIndex (even_iff_two_dvd.mp he)
  refine ⟨h711.elemAbelian, h711.noncyclic, h711.ti, ?_, ?_, ?_⟩
  · refine ⟨le_top, hchar, ?_⟩
    exact hoddT.of_dvd_nat (Subgroup.relIndex_dvd_of_le_left
      (H := hatT1 D S) (K := (⊤ : Subgroup (VG (D.img H))) ⊓ N) (L := ⊤) hTle)
  · rintro ⟨-, hlepc⟩
    exact hnot hlepc
  · have hdvd : (hatT1 D S).relIndex ((⊤ : Subgroup (VG (D.img H))) ⊓ N) ∣
        (hatT1 D S).relIndex (⊤ : Subgroup (VG (D.img H))) :=
      ⟨((⊤ : Subgroup (VG (D.img H))) ⊓ N).relIndex (⊤ : Subgroup (VG (D.img H))),
        by rw [Subgroup.relIndex_mul_relIndex
          (H := hatT1 D S) (K := (⊤ : Subgroup (VG (D.img H))) ⊓ N) (L := ⊤) hTle le_top]⟩
    exact ⟨hTle, hsy.isPGroup, fun h2 => hsy.not_dvd_relIndex (dvd_trans h2 hdvd)⟩

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
