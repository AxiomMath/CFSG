module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSMin
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBSyl
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

@[expose] noncomputable def hatW0 (D : ModDataE H (iSub16 V H)) (V S : Subgroup G) :
    Subgroup (LGL 2 D.W) :=
  ⨆ B ∈ {B : Subgroup (LGL 2 D.W) | B ∈ hatGamma D V ∧ B ≤ D.img S}, B

private theorem w16l_mem_normalizer_subgroupOf {X : Type*} [Group X] {L A : Subgroup X}
    (hA : A ≤ L) {g : L} :
    g ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup L) : Set L) ↔
      (g : X) ∈ Subgroup.normalizer (A : Set X) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hA, Subgroup.mem_subgroupOf]

private theorem w16l_cj_hatW0_le_of_forall (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {g : LGL 2 D.W} (hgH : g ∈ D.img H)
    (hgen : ∀ B ∈ {B : Subgroup (LGL 2 D.W) | B ∈ hatGamma D V ∧ B ≤ D.img S},
      cj g B ≤ D.img S) :
    cj g (hatW0 D V S) ≤ hatW0 D V S := by
  have hass := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  rw [show cj g (hatW0 D V S) = (hatW0 D V S).map (MulAut.conj g).toMonoidHom from rfl]
  unfold hatW0
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup]
  refine iSup_le fun B => iSup_le fun hB => ?_
  exact le_iSup_of_le (cj g B)
    (le_iSup_of_le ⟨hass.invariant B hB.1 g hgH, hgen B hB⟩ le_rfl)

theorem IsMinFam16.hat_normalizer_W0_le (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ n ∈ D.img H,
      n ∈ Subgroup.normalizer ((hatW0 D V S : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) →
      n ∈ Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hV_le_L : D.img V ≤ D.img H := D.img_mono hVH
  have hhatW0_le_L : hatW0 D V S ≤ D.img H := by
    unfold hatW0
    refine iSup_le fun B => iSup_le fun hB => ?_
    obtain ⟨x, hx, rfl⟩ := hB.1
    exact D.img_mono (conjSubgroup_le_of_le hVH hx)
  let L : Subgroup (LGL 2 D.W) := D.img H
  let φ : ↥H →* ↥L := D.ρ.codRestrict L fun j => D.mem_img.2 ⟨j, j.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨j, _hj, hjx⟩ := D.mem_img.1 x.2
    exact ⟨j, Subtype.ext hjx⟩
  let A : Subgroup ↥L := (D.img V).subgroupOf L
  let W : Subgroup ↥L := (hatW0 D V S).subgroupOf L
  have hass := Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hV_mem_Gamma : D.img V ∈ hatGamma D V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hA_ne_bot : A ≠ ⊥ := by
    intro hbot
    apply hass.ne_bot (D.img V) hV_mem_Gamma
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hV_le_L hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ A := hx
    rw [hbot] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
  have hAW : A ≤ W := Subgroup.subgroupOf_mono L (by
    unfold hatW0
    exact le_iSup_of_le (D.img V)
      (le_iSup_of_le ⟨hV_mem_Gamma, D.img_mono h.V_le_S⟩ le_rfl))
  have hAcore : A ⊓ CFSG.pCore 2 ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : LGL 2 D.W) ∈ D.img V ⊓ pCoreOf 2 (D.img H) :=
      ⟨Subgroup.mem_subgroupOf.mp hx.1, (CFSG.mem_openPCoreOf_iff x).mpr hx.2⟩
    rw [hass.inf_pCore (D.img V) hV_mem_Gamma] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext (Subgroup.mem_bot.1 hx'))
  have hW : IsPGroup 2 W := by
    have himgS : IsPGroup 2 (D.img S) := D.isPGroup_img h.sylow.isPGroup
    refine (himgS.comap_subtype (K := L)).to_le (Subgroup.subgroupOf_mono L ?_)
    unfold hatW0
    exact iSup_le fun B => iSup_le fun hB => hB.2
  have hS_norm : (S.subgroupOf H).map φ ≤ Subgroup.normalizer (W : Set ↥L) := by
    rintro x ⟨j, hj, rfl⟩
    have hjS : (j : G) ∈ S := Subgroup.mem_subgroupOf.mp hj
    have hgS : D.ρ j ∈ D.img S := D.mem_img.2 ⟨j, hjS, rfl⟩
    have hgH : D.ρ j ∈ D.img H := D.mem_img.2 ⟨j, j.2, rfl⟩
    have hle := w16l_cj_hatW0_le_of_forall h1 h5 hS h hH hV D hgH (fun B hB => by
      rintro z ⟨b, hb, rfl⟩
      exact (D.img S).mul_mem ((D.img S).mul_mem hgS (hB.2 hb)) ((D.img S).inv_mem hgS))
    have hnorm : D.ρ j ∈ Subgroup.normalizer (hatW0 D V S : Set (LGL 2 D.W)) := by
      refine Subgroup.mem_normalizer_fintype ?_
      intro y hy
      exact hle (Subgroup.mem_map_of_mem (MulAut.conj (D.ρ j)).toMonoidHom hy)
    exact (w16l_mem_normalizer_subgroupOf hhatW0_le_L).mpr hnorm
  have hPre := w16l_normalizer_preimage_le hH φ hφ A W hA_ne_bot hAW hAcore hW hS_norm
  intro n hnH hnNorm
  obtain ⟨j, _hj, hjn⟩ := D.mem_img.1 hnH
  have hnormW : (⟨n, hnH⟩ : ↥L) ∈ Subgroup.normalizer (W : Set ↥L) :=
    (w16l_mem_normalizer_subgroupOf hhatW0_le_L).mpr hnNorm
  have hφj : φ j = (⟨n, hnH⟩ : ↥L) := Subtype.ext hjn
  have hjN : j ∈ (Subgroup.normalizer (W : Set ↥L)).comap φ := by
    rw [Subgroup.mem_comap, hφj]
    exact hnormW
  have hjM : (j : G) ∈ M := Subgroup.mem_subgroupOf.mp (hPre hjN)
  have hnormV : (j : G) ∈ Subgroup.normalizer (V : Set G) := by
    rw [h.hyp.h6.normalizer_eq]
    exact hjM
  have hconjV : conjSubgroup V ((j : G)⁻¹) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (V : Set G)).inv_mem hnormV)
  have hcj : cj n (D.img V) = D.img V := by
    rw [← hjn, D.img_conj hVH j, hconjV]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hcj

theorem IsMinFam16.hatX_normalizer_le (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∀ d ∈ Subgroup.normalizer ((hatP D V S : Subgroup (hatX D V)) : Set (hatX D V)),
      d ∈ Subgroup.normalizer ((hatS D V : Subgroup (hatX D V)) : Set (hatX D V)) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  have hK_le_H : CFSG.Quasithin.conjClosure V H ≤ H :=
    CFSG.Quasithin.conjClosure_le fun g hg z hz =>
      H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hVK : D.img V ≤ hatK D V := D.img_mono (CFSG.Quasithin.le_conjClosure V H)
  have hSK : D.img S ⊓ hatK D V ≤ hatK D V := inf_le_right
  intro d hd
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK D V)) d
  have hd' : QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)) k ∈
      Subgroup.normalizer ((hatP D V S : Subgroup (hatX D V)) : Set (hatX D V)) := by
    rw [hk]
    exact hd
  have hQ_le_T' : CFSG.pCore 2 ↥(hatK D V) ≤
      (D.img S ⊓ hatK D V).subgroupOf (hatK D V) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxK : (x : LGL 2 D.W) ∈ pCoreOf 2 (hatK D V) :=
      (CFSG.mem_openPCoreOf_iff x).mpr hx
    have hle1 : pCoreOf 2 (hatK D V) ≤ pCoreOf 2 (D.img H) :=
      CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (D.img_mono hK_le_H)
        (D.img_le_normalizer le_rfl hK_le_H (CFSG.Quasithin.le_normalizer_conjClosure V H))
    have hle2 : pCoreOf 2 (D.img H) ≤ D.img S :=
      CFSG.Quasithin.pCoreOf_le_of_isSylowIn
        (D.isSylowIn_img_of_isSylowIn (h.isSylowIn_of_fam h1 hS hH.1))
    exact ⟨hle2 (hle1 hxK), CFSG.LieType.BorelTits.pCoreOf_le 2 _ hxK⟩
  have hk_norm_T' : k ∈ Subgroup.normalizer
      (((D.img S ⊓ hatK D V).subgroupOf (hatK D V)) : Set ↥(hatK D V)) := by
    have hcomap : (hatP D V S).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))) =
        (D.img S ⊓ hatK D V).subgroupOf (hatK D V) := by
      unfold hatP
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hQ_le_T'
    have hmem : k ∈ (Subgroup.normalizer
        ((hatP D V S : Subgroup (hatX D V)) : Set (hatX D V))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V))) :=
      Subgroup.mem_comap.mpr hd'
    have hmem2 := Subgroup.le_normalizer_comap
      (f := QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
      (H := (hatP D V S : Subgroup (hatX D V))) hmem
    rwa [hcomap] at hmem2
  have hk_norm_That : (k : LGL 2 D.W) ∈ Subgroup.normalizer
      ((D.img S ⊓ hatK D V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) :=
    (w16l_mem_normalizer_subgroupOf hSK).mp hk_norm_T'
  have hk_imgH : (k : LGL 2 D.W) ∈ D.img H := D.img_mono hK_le_H k.2
  have hk_norm_W0 : (k : LGL 2 D.W) ∈
      Subgroup.normalizer (hatW0 D V S : Set (LGL 2 D.W)) := by
    have hcjT : cj (k : LGL 2 D.W) (D.img S ⊓ hatK D V) = (D.img S ⊓ hatK D V) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hk_norm_That
    have hle := w16l_cj_hatW0_le_of_forall h1 h5 hS h hH hV D hk_imgH (fun B hB => by
      have hBK : B ≤ hatK D V := by
        obtain ⟨x, hx, rfl⟩ := hB.1
        exact D.img_mono (conjSubgroup_le_conjClosure V H hx)
      calc cj (k : LGL 2 D.W) B ≤ cj (k : LGL 2 D.W) (D.img S ⊓ hatK D V) :=
            cj_mono _ (le_inf hB.2 hBK)
        _ = D.img S ⊓ hatK D V := hcjT
        _ ≤ D.img S := inf_le_left)
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    exact hle (Subgroup.mem_map_of_mem (MulAut.conj (k : LGL 2 D.W)).toMonoidHom hy)
  have hk_norm_V : (k : LGL 2 D.W) ∈
      Subgroup.normalizer ((D.img V : Subgroup (LGL 2 D.W)) : Set (LGL 2 D.W)) :=
    IsMinFam16.hat_normalizer_W0_le h1 h5 hS h hH hV D (k : LGL 2 D.W) hk_imgH hk_norm_W0
  have hk_norm_Vsub : k ∈ Subgroup.normalizer
      (((D.img V).subgroupOf (hatK D V)) : Set ↥(hatK D V)) :=
    (w16l_mem_normalizer_subgroupOf hVK).mpr hk_norm_V
  have hd_norm : QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)) k ∈
      Subgroup.normalizer ((hatS D V : Subgroup (hatX D V)) : Set (hatX D V)) :=
    Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK D V)))
      (Subgroup.mem_map_of_mem _ hk_norm_Vsub)
  rwa [hk] at hd_norm

end CFSG.LocalAnalysis.WeakClosure81

end
