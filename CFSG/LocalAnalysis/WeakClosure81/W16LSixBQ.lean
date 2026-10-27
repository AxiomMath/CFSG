module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixSeven
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBQA
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NOneC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.pCoreOf_hatK_le_centralizer (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ A ∈ D.conjImgFam V,
      pCoreOf 2 (hatK D V) ≤ Subgroup.centralizer (A : Set (LGL 2 D.W)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun y hy z hz =>
      H.mul_mem (H.mul_mem hy (hVH hz)) (H.inv_mem hy)
  have hass : Assumption131 (D.img H) (D.conjImgFam V) (D.conjImgSpace V₀ V)
      (mRank (D.img V)) := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hVmem : D.img V ∈ D.conjImgFam V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hpCore_le : pCoreOf 2 (hatK D V) ≤ pCoreOf 2 (D.img H) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (D.img_mono hKH)
      (D.img_le_normalizer le_rfl hKH (CFSG.Quasithin.le_normalizer_conjClosure V H))
  have hKhatN : D.img H ≤ Subgroup.normalizer (hatK D V : Set (LGL 2 D.W)) :=
    D.img_le_normalizer le_rfl hKH (CFSG.Quasithin.le_normalizer_conjClosure V H)
  have hH_le_NQ : D.img H ≤
      Subgroup.normalizer (pCoreOf 2 (hatK D V) : Set (LGL 2 D.W)) :=
    hKhatN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (hatK D V))
  have hVhat_le_NQ : D.img V ≤
      Subgroup.normalizer (pCoreOf 2 (hatK D V) : Set (LGL 2 D.W)) :=
    (D.img_mono hVH).trans hH_le_NQ
  have hSH : IsSylowIn 2 S H := h.isSylowIn_of_fam h1 hS hH.1
  have hSHat : IsSylowIn 2 (D.img S) (D.img H) := D.isSylowIn_img_of_isSylowIn hSH
  have hQ0_le_S : pCoreOf 2 (D.img H) ≤ D.img S :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSHat
  have hSNV : S ≤ Subgroup.normalizer (V : Set G) :=
    h.S_le_M.trans (le_of_eq h.hyp.h6.normalizer_eq.symm)
  have hS_le_NVhat : D.img S ≤ Subgroup.normalizer (D.img V : Set (LGL 2 D.W)) :=
    D.img_le_normalizer hH.1.1 hVH hSNV
  have hQ_le_NVhat : pCoreOf 2 (hatK D V) ≤
      Subgroup.normalizer (D.img V : Set (LGL 2 D.W)) :=
    hpCore_le.trans (hQ0_le_S.trans hS_le_NVhat)
  have hQV_le_Q : ⁅pCoreOf 2 (hatK D V), D.img V⁆ ≤ pCoreOf 2 (hatK D V) := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp hVhat_le_NQ
  have hQV_le_V : ⁅pCoreOf 2 (hatK D V), D.img V⁆ ≤ D.img V :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hQ_le_NVhat
  have hQVbot : ⁅pCoreOf 2 (hatK D V), D.img V⁆ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ (D.img V) ⊓ pCoreOf 2 (D.img H) :=
      ⟨hQV_le_V hz, hpCore_le (hQV_le_Q hz)⟩
    rw [hass.inf_pCore (D.img V) hVmem] at hz'
    exact hz'
  rintro A ⟨x, hxH, rfl⟩
  let r : LGL 2 D.W := D.ρ (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H)
  have hBmap : (D.img V).map (MulAut.conj r).toMonoidHom = D.img (conjSubgroup V x) := by
    change cj r (D.img V) = D.img (conjSubgroup V x)
    simpa [r] using D.img_conj hVH (⟨x⁻¹, H.inv_mem hxH⟩ : ↥H)
  have hQmap : (pCoreOf 2 (hatK D V)).map (MulAut.conj r).toMonoidHom =
      pCoreOf 2 (hatK D V) := by
    have hr : r ∈ D.img H :=
      D.mem_img.2 ⟨⟨x⁻¹, H.inv_mem hxH⟩, H.inv_mem hxH, rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH_le_NQ hr)
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_
  rw [← hBmap, ← hQmap, ← Subgroup.map_commutator (H₁ := pCoreOf 2 (hatK D V))
    (H₂ := D.img V) (MulAut.conj r).toMonoidHom, hQVbot, Subgroup.map_bot]

section Certified

theorem IsMinFam16.UAOf_conj_of_congr (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {B B' : Subgroup (LGL 2 D.W)} (hB : B ∈ hatGamma D V)
    (hB' : B' ∈ hatGamma D V) {β β' : LGL 2 D.W} (hβ : β ∈ B) (hβ1 : β ≠ 1) (hβ' : β' ∈ B')
    (hq : β⁻¹ * β' ∈ pCoreOf 2 (hatK D V)) :
    ∃ x ∈ pCoreOf 2 (kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H))),
      UAOf (D.img H) (hatVA D V₀ V) B' =
        CFSG.Quasithin.conjSubgroup (UAOf (D.img H) (hatVA D V₀ V) B) x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun y hy z hz =>
      H.mul_mem (H.mul_mem hy (hVH hz)) (H.inv_mem hy)
  have hass : Assumption131 (D.img H) (hatGamma D V) (hatVA D V₀ V) (mRank (D.img V)) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank : ∀ A ∈ hatGamma D V, mRank A ≤ mRank (D.img V) :=
    Cex16.mRank_le_iSub16 h hH.1 D
  have hVAle : ∀ A ∈ hatGamma D V, hatVA D V₀ V A ≤ fixSub A :=
    Cex16.conjImgSpace_le_fixSub_iSub16 h1 h5 hS h hH.1 hV D
  have htrans : ∀ A ∈ hatGamma D V, ∀ B ∈ hatGamma D V, ∃ g ∈ D.img H, B = cj g A :=
    hatGamma_transitive D V hVH
  have hA₀ : D.img V ∈ hatGamma D V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have h711 : SevenK.Hyp711 (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) :=
    IsMinFam16.hyp711_img h1 h5 hS h hH hV D
  have hcore_le : pCoreOf 2 (kHatOf (hatGamma D V)) ≤ pCoreOf 2 (D.img H) := by
    rw [kHatOf_hatGamma_eq D V hVH]
    exact CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (D.img_mono hKH)
      (D.img_le_normalizer le_rfl hKH (CFSG.Quasithin.le_normalizer_conjClosure V H))
  have hq' : β⁻¹ * β' ∈ pCoreOf 2 (kHatOf (hatGamma D V)) := by
    rw [kHatOf_hatGamma_eq D V hVH]
    exact hq
  have hres := w16l_UAOf_conj_of_congr hass hrank hVAle htrans hA₀
    (by simpa only [hatV1] using h711) hcore_le hB hB' hβ hβ1 hβ' hq'
  simpa only [hatV1] using hres

theorem IsMinFam16.hat_normalizer_sup_Q (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {g : G} (hg : g ∈ H) :
    ∀ a ∈ D.img H, a ∈ Subgroup.normalizer
      ((D.img (conjSubgroup V g) ⊔ pCoreOf 2 (hatK D V) : Subgroup (LGL 2 D.W)) :
        Set (LGL 2 D.W)) →
      a ∈ Subgroup.normalizer
        ((D.img (conjSubgroup V g) : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha haN
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun y hy z hz =>
      H.mul_mem (H.mul_mem hy (hVH hz)) (H.inv_mem hy)
  have hass : Assumption131 (D.img H) (hatGamma D V) (hatVA D V₀ V) (mRank (D.img V)) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hpCore_le : pCoreOf 2 (hatK D V) ≤ pCoreOf 2 (D.img H) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (D.img_mono hKH)
      (D.img_le_normalizer le_rfl hKH (CFSG.Quasithin.le_normalizer_conjClosure V H))
  let B : Subgroup (LGL 2 D.W) := D.img (conjSubgroup V g)
  have hB : B ∈ hatGamma D V := ⟨g, hg, rfl⟩
  let Q : Subgroup (LGL 2 D.W) := pCoreOf 2 (hatK D V)
  let B' : Subgroup (LGL 2 D.W) := cj a B
  have hB' : B' ∈ hatGamma D V := hass.invariant B hB a ha
  have hQcent : Q ≤ Subgroup.centralizer (B : Set (LGL 2 D.W)) :=
    IsMinFam16.pCoreOf_hatK_le_centralizer h1 h5 hS h hH hV D B hB
  have hBNQ : B ≤ Subgroup.normalizer (Q : Set (LGL 2 D.W)) :=
    (Subgroup.le_centralizer_iff.mp hQcent).trans (Subgroup.centralizer_le_normalizer _)
  have hBQ : (↑(B ⊔ Q) : Set (LGL 2 D.W)) =
      (B : Set (LGL 2 D.W)) * (Q : Set (LGL 2 D.W)) :=
    Subgroup.coe_mul_of_left_le_normalizer_right B Q hBNQ
  have hB'le : B' ≤ B ⊔ Q := by
    have hmap : (B ⊔ Q : Subgroup (LGL 2 D.W)).map (MulAut.conj a).toMonoidHom = B ⊔ Q :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp haN
    calc B' = cj a B := rfl
      _ ≤ cj a (B ⊔ Q) := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) le_sup_left
      _ = B ⊔ Q := hmap
  obtain ⟨⟨β', hβ'mem⟩, hβ'ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hass.ne_bot B' hB')
  have hβ'1 : β' ≠ 1 := fun h1' => hβ'ne (Subtype.ext h1')
  have hβ'BQ : β' ∈ (B : Set (LGL 2 D.W)) * (Q : Set (LGL 2 D.W)) := by
    rw [← hBQ]
    exact hB'le hβ'mem
  obtain ⟨β, hβ, q, hqQ, hβ'eq⟩ := hβ'BQ
  have hβ1 : β ≠ 1 := by
    intro hβEq
    have hβ'Q : β' ∈ Q := by
      rw [← hβ'eq]
      simpa [hβEq] using hqQ
    have hβ'Q0 : β' ∈ pCoreOf 2 (D.img H) := hpCore_le hβ'Q
    have hbot : β' ∈ (⊥ : Subgroup (LGL 2 D.W)) := by
      have hmem : β' ∈ B' ⊓ pCoreOf 2 (D.img H) := ⟨hβ'mem, hβ'Q0⟩
      rwa [hass.inf_pCore B' hB'] at hmem
    exact hβ'1 (Subgroup.mem_bot.1 hbot)
  have hq : β⁻¹ * β' ∈ pCoreOf 2 (hatK D V) := by
    have heq : β⁻¹ * β' = q := by rw [← hβ'eq]; group
    rwa [heq]
  obtain ⟨x, hxJ, hxeq⟩ := IsMinFam16.UAOf_conj_of_congr h1 h5 hS h hH hV D hB hB'
    hβ hβ1 hβ'mem hq
  have hmapB : (UAOf (D.img H) (hatVA D V₀ V) B).map (projG (D.img H)) = B :=
    map_projG_wHat_sup_aHat (G := D.img H) (W := hatVA D V₀ V B) (A := B) (hass.le_G B hB)
  have hmapB' : (UAOf (D.img H) (hatVA D V₀ V) B').map (projG (D.img H)) = B' :=
    map_projG_wHat_sup_aHat (G := D.img H) (W := hatVA D V₀ V B') (A := B')
      (hass.le_G B' hB')
  have hxK : x ∈ kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxJ
  have hprojxQ : projG (D.img H) x ∈ pCoreOf 2 (hatK D V) := by
    have h := (mem_pCoreOf_kSub_UAOf_orbit_iff hass (Cex16.mRank_le_iSub16 h hH.1 D)
      (hatGamma_transitive D V hVH) ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩ hxK).1 hxJ
    rwa [kHatOf_hatGamma_eq D V hVH] at h
  have hxcent : projG (D.img H) x ∈ Subgroup.centralizer (B : Set (LGL 2 D.W)) :=
    (IsMinFam16.pCoreOf_hatK_le_centralizer h1 h5 hS h hH hV D B hB) hprojxQ
  have hxN : projG (D.img H) x ∈ Subgroup.normalizer (B : Set (LGL 2 D.W)) :=
    Subgroup.centralizer_le_normalizer _ hxcent
  have hconjB : CFSG.Quasithin.conjSubgroup B (projG (D.img H) x) = B := by
    rw [CFSG.Quasithin.conjSubgroup]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (B : Set (LGL 2 D.W))).inv_mem hxN)
  have hproj_eq : B' = B := by
    calc B' = (UAOf (D.img H) (hatVA D V₀ V) B').map (projG (D.img H)) := hmapB'.symm
      _ = (CFSG.Quasithin.conjSubgroup (UAOf (D.img H) (hatVA D V₀ V) B) x).map
            (projG (D.img H)) := by rw [hxeq]
      _ = CFSG.Quasithin.conjSubgroup
            ((UAOf (D.img H) (hatVA D V₀ V) B).map (projG (D.img H)))
            (projG (D.img H) x) := by rw [map_conjSubgroup_hom]
      _ = CFSG.Quasithin.conjSubgroup B (projG (D.img H) x) := by rw [hmapB]
      _ = B := hconjB
  show a ∈ Subgroup.normalizer (B : Set (LGL 2 D.W))
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hproj_eq

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
