module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBQ
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineU3Hyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem w16l_hatVA_conjSubgroup (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {g : G} (hg : g ∈ H) :
    D.conjImgSpace V₀ V (D.img (conjSubgroup V g)) = D.sp (conjSubgroup V₀ g) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hass : Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  let j₀ : ↥H := ⟨g⁻¹, H.inv_mem hg⟩
  have hA : D.img V ∈ D.conjImgFam V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hgj : D.ρ j₀ ∈ D.img H := D.mem_img.2 ⟨j₀, j₀.2, rfl⟩
  have heq := hass.equivariant (D.img V) hA (D.ρ j₀) hgj
  have hbase := Cex16.conjImgSpace_img_eq h1 h5 hS h hH.1 hV D
  have hsp := D.conjSub_sp V₀ j₀
  have hconj := D.img_conj hVH j₀
  rw [hconj, hbase, hsp] at heq
  simpa [j₀] using heq

theorem IsMinFam16.hat_free (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {g : G} (hg : g ∈ H)
    (hnc : ∃ a ∈ D.img V, ∃ b ∈ D.img (conjSubgroup V g), a * b ≠ b * a) :
    ∀ a ∈ D.img V, a ∈ Subgroup.normalizer
      ((D.img (conjSubgroup V g) : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) → a = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hass : Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hnc' : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
    intro hall
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    obtain ⟨j, hjV, rfl⟩ := D.mem_img.1 ha
    obtain ⟨k, hkVg, rfl⟩ := D.mem_img.1 hb
    apply hab
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hall (j : G) hjV (k : G) hkVg)
  have hfive : V ⊓ conjSubgroup M g = U ⊔ V₀ := h5 hS h hH.1 hV g hg hnc'
  have hnormI : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hV0_le_I : V₀ ≤ iSub16 V H :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hH.1 hV)).trans
      (CFSG.Quasithin.le_conjClosure _ _)
  have hUVI : U ⊔ V₀ ≤ iSub16 V H := by
    rw [← Cex16.inf_iSub16_eq h1 h5 hS h hH.1 hV]
    exact inf_le_right
  have hV0g_le_I : conjSubgroup V₀ g ≤ iSub16 V H := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 : g * x * g⁻¹ ∈ iSub16 V H := hV0_le_I hx
    have h2 := (Subgroup.mem_normalizer_iff.1 (hnormI hg) x).2 h1
    exact h2
  have hVA_eq : D.conjImgSpace V₀ V (D.img (conjSubgroup V g)) = D.sp (conjSubgroup V₀ g) :=
    w16l_hatVA_conjSubgroup h1 h5 hS h hH hV D hg
  intro a ha hN
  obtain ⟨j, hjV, hja⟩ := D.mem_img.1 ha
  have hN' : D.ρ j ∈ Subgroup.normalizer
      ((D.img (conjSubgroup V g) : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) :=
    hja.symm ▸ hN
  have hBmem : D.img (conjSubgroup V g) ∈ D.conjImgFam V := ⟨g, hg, rfl⟩
  have hstab : D.ρ j ∈ stabilizerOf (D.img H)
      (D.conjImgSpace V₀ V (D.img (conjSubgroup V g))) := by
    rw [← hass.normalizer_eq (D.img (conjSubgroup V g)) hBmem]
    exact ⟨D.mem_img.2 ⟨j, hVH hjV, rfl⟩, hN'⟩
  have hfix : conjSub (D.ρ j) (D.sp (conjSubgroup V₀ g)) = D.sp (conjSubgroup V₀ g) := by
    rw [← hVA_eq]
    exact hstab.2
  have hmem_sp : ∀ x ∈ conjSubgroup V₀ g, (j : G) * x * (j : G)⁻¹ ∈ conjSubgroup V₀ g := by
    intro x hx
    have hxI : x ∈ iSub16 V H := hV0g_le_I hx
    have hxsp : D.ι x ∈ D.sp (conjSubgroup V₀ g) := ⟨x, ⟨hx, hxI⟩, rfl⟩
    have hmap : D.ρ j (D.ι x) ∈ D.sp (conjSubgroup V₀ g) := by
      rw [← hfix]
      exact Submodule.mem_map.2 ⟨D.ι x, hxsp, rfl⟩
    rw [D.ρ_ι j x hxI] at hmap
    have hjeI : (j : G) * x * (j : G)⁻¹ ∈ iSub16 V H :=
      (Subgroup.mem_normalizer_iff.1 (hnormI j.2) x).1 hxI
    obtain ⟨e, he, hι⟩ := D.mem_sp.1 hmap
    rw [← D.ι_injOn he.2 hjeI hι]
    exact he.1
  have hj2 : (j : G) * (j : G) = 1 := by
    have := h.hyp.h6.elemAbelian.2 (j : G) hjV
    simpa [pow_two] using this
  have hnorm : (j : G) ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hmem_sp x hx, fun hx => ?_⟩
    have hjj : (j : G) * ((j : G) * x * (j : G)⁻¹) * (j : G)⁻¹ = x := by
      have h1 : (j : G) * ((j : G) * x * (j : G)⁻¹) * (j : G)⁻¹ =
          ((j : G) * (j : G)) * x * ((j : G)⁻¹ * (j : G)⁻¹) := by group
      rw [h1, show (j : G)⁻¹ * (j : G)⁻¹ = ((j : G) * (j : G))⁻¹ by rw [mul_inv_rev],
        hj2, inv_one, one_mul, mul_one]
    rw [← hjj]
    exact hmem_sp ((j : G) * x * (j : G)⁻¹) hx
  have hjM : (j : G) ∈ conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer V₀ g, h.hyp.normalizer₀] at hnorm
    exact hnorm
  have hjVD : (j : G) ∈ U ⊔ V₀ := by
    rw [← hfive]
    exact ⟨hjV, hjM⟩
  have hjI : (j : G) ∈ iSub16 V H := hUVI hjVD
  have hρj : D.ρ j = 1 :=
    (D.ρ_eq_one_iff j).2
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (h.isElemAbelian_iSub16 h1 hS hH.1).1 hjI)
  rw [← hja]
  exact hρj

section Certified


theorem IsMinFam16.hatX_free (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ x : hatX D V,
      (∃ a ∈ hatS D V, ∃ b ∈ conjSubgroup (hatS D V) x, a * b ≠ b * a) →
      ∀ a ∈ hatS D V, a ∈ Subgroup.normalizer
        ((conjSubgroup (hatS D V) x : Subgroup (hatX D V)) : Set (hatX D V)) → a = 1 := by
  classical
  intro x hnc a ha haN
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun y hy z hz =>
      H.mul_mem (H.mul_mem hy (hVH hz)) (H.inv_mem hy)
  let mk := QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))
  obtain ⟨k, hkx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)) x
  obtain ⟨j, hjK, hjk⟩ := D.mem_img.1 k.2
  have hjH : (j : G) ∈ H := hKH hjK
  let Bx : Subgroup (LGL 2 D.W) := D.img (conjSubgroup V (j : G))
  have hBxK : Bx ≤ hatK D V := by
    refine D.img_mono ?_
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have hmem := CFSG.Quasithin.mem_conjClosure (H.inv_mem hjH) hz
    have e : (j : G)⁻¹ * ((j : G) * z * (j : G)⁻¹) * ((j : G)⁻¹)⁻¹ = z := by group
    rwa [e] at hmem
  have hconj_eq : CFSG.Quasithin.conjSubgroup (hatS D V) x =
      SevenK.barSub (hatK D V) mk Bx := by
    rw [← hkx]
    change CFSG.Quasithin.conjSubgroup
      (SevenK.barSub (hatK D V) mk (D.img V)) (mk k) = _
    rw [← barSub_conjSubgroup mk (D.img V) k]
    congr 1
    rw [← hjk]
    have h := D.img_conj hVH (⟨j⁻¹, H.inv_mem hjH⟩ : ↥H)
    rw [show D.ρ (⟨j⁻¹, H.inv_mem hjH⟩ : ↥H) = (D.ρ j)⁻¹ by
      rw [show (⟨j⁻¹, H.inv_mem hjH⟩ : ↥H) = (⟨j, hjH⟩ : ↥H)⁻¹ by ext; simp, map_inv]] at h
    have hgoal : CFSG.Quasithin.conjSubgroup (D.img V) (D.ρ j) =
        cj (D.ρ j)⁻¹ (D.img V) := rfl
    rw [hgoal]
    simpa [Bx] using h
  obtain ⟨â, hâV, hâa⟩ := SevenK.mem_barSub.1
    (show a ∈ SevenK.barSub (hatK D V) mk (D.img V) from ha)
  have haN' : a ∈ Subgroup.normalizer
      ((SevenK.barSub (hatK D V) mk Bx : Subgroup (hatX D V)) : Set (hatX D V)) := by
    rw [hconj_eq] at haN
    exact haN
  have hmem : â ∈ (Subgroup.normalizer
      ((SevenK.barSub (hatK D V) mk Bx : Subgroup (hatX D V)) :
        Set (hatX D V))).comap mk := by
    rw [Subgroup.mem_comap, hâa]
    exact haN'
  have hmem2 : â ∈ Subgroup.normalizer
      (((SevenK.barSub (hatK D V) mk Bx).comap mk : Subgroup ↥(hatK D V)) :
        Set ↥(hatK D V)) :=
    Subgroup.le_normalizer_comap (f := mk) hmem
  have hpCoreK : pCoreOf 2 (hatK D V) ≤ hatK D V :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hcomap : (SevenK.barSub (hatK D V) mk Bx).comap mk =
      (Bx ⊔ pCoreOf 2 (hatK D V)).subgroupOf (hatK D V) := by
    rw [SevenK.barSub, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      ← CFSG.openPCoreOf_subgroupOf, ← Subgroup.subgroupOf_sup hBxK hpCoreK]
  rw [hcomap] at hmem2
  have hBxQK : Bx ⊔ pCoreOf 2 (hatK D V) ≤ hatK D V := sup_le hBxK hpCoreK
  have hâN : (â : LGL 2 D.W) ∈ Subgroup.normalizer
      ((Bx ⊔ pCoreOf 2 (hatK D V) : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hBxQK] at hmem2
    exact Subgroup.mem_subgroupOf.mp hmem2
  have hâimgH : (â : LGL 2 D.W) ∈ D.img H := D.img_mono hKH â.2
  have hâNBx : (â : LGL 2 D.W) ∈ Subgroup.normalizer (Bx : Set (LGL 2 D.W)) :=
    IsMinFam16.hat_normalizer_sup_Q h1 h5 hS h hH hV D hjH (â : LGL 2 D.W) hâimgH hâN
  have hnc' : ∃ a' ∈ D.img V, ∃ b' ∈ Bx, a' * b' ≠ b' * a' := by
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := hnc
    obtain ⟨a0, ha0V, ha0a⟩ := SevenK.mem_barSub.1
      (show a₀ ∈ SevenK.barSub (hatK D V) mk (D.img V) from ha₀)
    have hb0' : b₀ ∈ SevenK.barSub (hatK D V) mk Bx := by
      rw [← hconj_eq]
      exact hb₀
    obtain ⟨b0, hb0Bx, hb0b⟩ := SevenK.mem_barSub.1 hb0'
    refine ⟨(a0 : LGL 2 D.W), ha0V, (b0 : LGL 2 D.W), hb0Bx, ?_⟩
    intro hcomm
    apply hab
    rw [← ha0a, ← hb0b, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hâ1 : (â : LGL 2 D.W) = 1 :=
    IsMinFam16.hat_free h1 h5 hS h hH hV D hjH hnc' (â : LGL 2 D.W) hâV hâNBx
  have hâ1' : â = 1 := Subtype.ext hâ1
  rw [← hâa, hâ1', map_one]

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
