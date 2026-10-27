module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2G1Seven
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Defs

variable {H E : Subgroup G} (Mo : ModDataE H E) (V : Subgroup G)

@[expose] def hatBar : ↥(hatK Mo V) →* hatX Mo V ⧸ Subgroup.center (hatX Mo V) :=
  (QuotientGroup.mk' (Subgroup.center (hatX Mo V))).comp
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(hatK Mo V)))

@[expose] def hatBarSub (J : Subgroup G) : Subgroup (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) :=
  ((Mo.img J).subgroupOf (hatK Mo V)).map (hatBar Mo V)

theorem hatBar_surjective : Function.Surjective (hatBar Mo V) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem mem_hatBarSub_iff {J : Subgroup G} {y : hatX Mo V ⧸ Subgroup.center (hatX Mo V)} :
    y ∈ hatBarSub Mo V J ↔
      ∃ x : ↥(hatK Mo V), (x : LGL 2 Mo.W) ∈ Mo.img J ∧ hatBar Mo V x = y := by
  unfold hatBarSub
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem hatS_map_eq_hatBarSub :
    (hatS Mo V).map (QuotientGroup.mk' (Subgroup.center (hatX Mo V))) = hatBarSub Mo V V := by
  unfold hatS hatBarSub hatBar
  rw [Subgroup.map_map]

end Defs

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section NoCert

theorem pCore_hatK_le_center (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    CFSG.pCore 2 ↥(hatK Mo V) ≤ Subgroup.center ↥(hatK Mo V) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a ha
  rw [Subgroup.mem_center_iff]
  intro x
  let A : Subgroup (LGL 2 Mo.W) := pCoreOf 2 (hatK Mo V)
  have hA_le_hatK : A ≤ hatK Mo V := CFSG.LieType.BorelTits.pCoreOf_le 2 (hatK Mo V)
  have hA_le_imgH : A ≤ Mo.img H := hA_le_hatK.trans (Mo.img_mono c.conjClosure_le_H)
  have hAp : IsPGroup 2 A := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (hatK Mo V)
  have hAeq : ∀ h ∈ Mo.img H, A.map (MulAut.conj h).toMonoidHom = A := by
    intro h hh
    have hcjK : cj h (hatK Mo V) = hatK Mo V := by
      obtain ⟨j, -, rfl⟩ := Mo.mem_img.mp hh
      rw [Mo.img_conj (A := conjClosure V H) c.conjClosure_le_H j,
        conjSubgroup_eq_iff_mem_normalizer.mpr
          (Subgroup.inv_mem _ (le_normalizer_conjClosure V H j.2))]
    change (pCoreOf 2 (hatK Mo V)).map (MulAut.conj h).toMonoidHom =
      pCoreOf 2 (hatK Mo V)
    rw [← CFSG.QuasithinUnique.pCoreOf_map_equiv 2 (MulAut.conj h) (hatK Mo V),
      show (hatK Mo V).map (MulAut.conj h).toMonoidHom = hatK Mo V from hcjK]
  have hnormA : Mo.img H ≤ Subgroup.normalizer (A : Set (LGL 2 Mo.W)) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hAeq h hh
  have hAn : (A.subgroupOf (Mo.img H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnormA
  obtain ⟨X, hCHX, hXH, hXn, hXrel, hXimg⟩ :=
    Mo.exists_normal_preimage_of_pGroup (A := A) hA_le_imgH hAn hAp
  let Y : Subgroup G := X ⊓ conjClosure V H
  have hKn : ((conjClosure V H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_conjClosure V H)
  have hYn : (Y.subgroupOf H).Normal := by
    have hsub : Y.subgroupOf H = (X.subgroupOf H) ⊓ ((conjClosure V H).subgroupOf H) := by
      ext y
      simp only [Y, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [hsub]
    exact Subgroup.normal_inf_normal _ _
  have hKY : conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ≤ Y :=
    le_inf (inf_le_right.trans hCHX) inf_le_left
  have hYK : Y ≤ conjClosure V H := inf_le_right
  have hKCH : conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) =
      (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ⊓ Y := by
    apply le_antisymm
    · rintro z ⟨hzK, hzCH⟩
      exact ⟨hzCH, hCHX hzCH, hzK⟩
    · rintro z ⟨hzCH, hzX, hzK⟩
      exact ⟨hzK, hzCH⟩
  have hCHnormH : H ≤ Subgroup.normalizer
      ((H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) : Set G) := by
    intro h hh
    exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hh)
      (le_normalizer_conjClosure (U ⊔ V₀) H hh)
  have hCHsubNormal : (((H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).subgroupOf X)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hXH.trans hCHnormH)
  have hdvd : (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex Y ∣
      (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex X := by
    haveI : (((H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).subgroupOf X)).Normal :=
      hCHsubNormal
    have hdvd' := Subgroup.relIndex_dvd_index_of_normal
      (H := (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).subgroupOf X)
      (K := Y.subgroupOf X)
    rw [Subgroup.relIndex_subgroupOf (H := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))
      (K := Y) (L := X) inf_le_left] at hdvd'
    simpa only [Subgroup.relIndex] using hdvd'
  obtain ⟨k, hk⟩ := hXrel
  have hY2 : ∃ k : ℕ, (conjClosure V H ⊓
      (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))).relIndex Y = 2 ^ k := by
    have hdvd2 : (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex Y ∣ 2 ^ k := by
      rw [← hk]
      exact hdvd
    obtain ⟨k', -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    refine ⟨k', ?_⟩
    rw [hKCH, Subgroup.inf_relIndex_right, hk']
  have hcommY : ⁅Y, conjClosure V H⁆ ≤
      H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
    c.comm_le_of_relIndex_two_pow h1 h5 h15 hS hYn hKY hYK hY2
  have haA : (a : LGL 2 Mo.W) ∈ A := by
    change (a : LGL 2 Mo.W) ∈ (CFSG.pCore 2 ↥(hatK Mo V)).map (hatK Mo V).subtype
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have haX : (a : LGL 2 Mo.W) ∈ Mo.img X := by
    simpa only [← hXimg] using haA
  obtain ⟨j, hjX, hja⟩ := Mo.mem_img.mp haX
  obtain ⟨j', hj'K, hj'a⟩ := Mo.mem_img.mp a.2
  have hρ_one : Mo.ρ (j⁻¹ * j') = 1 := by
    rw [map_mul, map_inv, hja, hj'a]
    group
  have hjj'_CH : (((j⁻¹ * j' : ↥H) : G)) ∈
      H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) :=
    ⟨(j⁻¹ * j').2, (Mo.ρ_eq_one_iff (j⁻¹ * j')).1 hρ_one⟩
  have hj'X : (j' : G) ∈ X := by
    have hmul : (j : G) * (((j⁻¹ * j' : ↥H) : G)) = (j' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← hmul]
    exact X.mul_mem hjX (hCHX hjj'_CH)
  have hj'Y : (j' : G) ∈ Y := ⟨hj'X, hj'K⟩
  obtain ⟨k, hkK, hkx⟩ := Mo.mem_img.mp x.2
  have hjk_mem : (((⁅j', k⁆ : ↥H) : G)) ∈ ⁅Y, conjClosure V H⁆ := by
    show ⁅(j' : G), (k : G)⁆ ∈ ⁅Y, conjClosure V H⁆
    exact Subgroup.commutator_mem_commutator hj'Y hkK
  have hjk_CH : (((⁅j', k⁆ : ↥H) : G)) ∈
      H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := hcommY hjk_mem
  have hρ_jk : Mo.ρ ⁅j', k⁆ = 1 := (Mo.ρ_eq_one_iff ⁅j', k⁆).2 hjk_CH.2
  have hcomm_ax : (⁅a, x⁆ : ↥(hatK Mo V)) = 1 := by
    apply Subtype.ext
    change ⁅(a : LGL 2 Mo.W), (x : LGL 2 Mo.W)⁆ = 1
    rw [← hj'a, ← hkx, ← map_commutatorElement]
    exact hρ_jk
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcomm_ax).symm

theorem not_comm_hat (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ¬ ∀ a ∈ Mo.img V, ∀ b ∈ Mo.img (conjSubgroup V g), a * b = b * a := by
  intro hcomm
  refine not_le_centralizer_conjClosure h1 h5 h15 hS c ?_
  intro v hv
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hconjVH : conjSubgroup V g ≤ H := by
    calc conjSubgroup V g ≤ conjSubgroup H g := E3.conjSubgroup_mono_left g hVH
      _ = H := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer c.g_mem.1)
  have hn : ∀ w ∈ conjSubgroup V g, v * w * v⁻¹ ∈
      conjSubgroup V g ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
    intro w hw
    have hwH : w ∈ H := hconjVH hw
    have hvH : v ∈ H := hVH hv
    have hxH : v * w * v⁻¹ ∈ H := H.mul_mem (H.mul_mem hvH hwH) (H.inv_mem hvH)
    refine (Mo.ρ_mem_img_iff hconjVH hxH).1 ?_
    have hval : Mo.ρ (⟨v * w * v⁻¹, hxH⟩ : ↥H) = Mo.ρ ⟨w, hwH⟩ := by
      have hcommvw := hcomm (Mo.ρ ⟨v, hvH⟩)
        (Mo.mem_img.mpr ⟨⟨v, hvH⟩, hv, rfl⟩) (Mo.ρ ⟨w, hwH⟩)
        (Mo.mem_img.mpr ⟨⟨w, hwH⟩, hw, rfl⟩)
      have he : (⟨v * w * v⁻¹, hxH⟩ : ↥H) = ⟨v, hvH⟩ * ⟨w, hwH⟩ * (⟨v, hvH⟩)⁻¹ := rfl
      rw [he, map_mul, map_mul, map_inv, hcommvw]
      group
    rw [hval]
    exact Mo.mem_img.mpr ⟨⟨w, hwH⟩, hw, rfl⟩
  have hvsup : v ∈ U ⊔ V₀ :=
    mem_sup_of_normalizes_conj h1 h5 h15 hS c c.g_mem c.g_not hv hn
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi
    (le_conjClosure (U ⊔ V₀) H hvsup)

end NoCert

section Certified


theorem isSimpleGroup_hatL (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    IsSimpleGroup ↥(Mo.img (V ⊔ conjSubgroup V g)) := by
  obtain ⟨hshape, -⟩ := c.hatL_shape h1 h5 h15 hS Mo c.g_mem c.g_not
  rcases hshape with hL2 | hSz | ⟨hn1, -⟩
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  · exfalso
    omega

theorem isPerfect_hatL (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    Group.IsPerfect ↥(Mo.img (V ⊔ conjSubgroup V g)) := by
  haveI hsimple : IsSimpleGroup ↥(Mo.img (V ⊔ conjSubgroup V g)) :=
    isSimpleGroup_hatL hn h1 h5 h15 hS c Mo
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator ↥(Mo.img (V ⊔ conjSubgroup V g))) with hbot | htop
  · exfalso
    have hcenter : Subgroup.center ↥(Mo.img (V ⊔ conjSubgroup V g)) = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top _).mp hbot
    have hab : ∀ a ∈ Mo.img V, ∀ b ∈ Mo.img (conjSubgroup V g), a * b = b * a := by
      intro a haV b hbW
      have haL : (⟨a, Mo.img_mono le_sup_left haV⟩ : ↥(Mo.img (V ⊔ conjSubgroup V g))) ∈
          Subgroup.center ↥(Mo.img (V ⊔ conjSubgroup V g)) := by rw [hcenter]; trivial
      have hcomm := (Subgroup.mem_center_iff.mp haL)
        (⟨b, Mo.img_mono le_sup_right hbW⟩ : ↥(Mo.img (V ⊔ conjSubgroup V g)))
      exact (Subtype.ext_iff.mp hcomm).symm
    exact not_comm_hat h1 h5 h15 hS c Mo hab
  · exact htop

theorem inf_center_hatL (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G) (h5 : W16Five G)
    (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) :
    ∀ x : ↥(hatK Mo V), (x : LGL 2 Mo.W) ∈ Mo.img (V ⊔ conjSubgroup V g) →
      x ∈ Subgroup.center ↥(hatK Mo V) → x = 1 := by
  intro x hxL hxcenter
  haveI hsimple : IsSimpleGroup ↥(Mo.img (V ⊔ conjSubgroup V g)) :=
    isSimpleGroup_hatL hn h1 h5 h15 hS c Mo
  let Lhat : Subgroup (LGL 2 Mo.W) := Mo.img (V ⊔ conjSubgroup V g)
  let Khat : Subgroup (LGL 2 Mo.W) := hatK Mo V
  have hLK : Lhat ≤ Khat := Mo.img_mono c.L_le_conjClosure
  let ι : ↥Lhat →* ↥Khat := Subgroup.inclusion hLK
  let N : Subgroup ↥Lhat := (Subgroup.center ↥Khat).comap ι
  haveI : N.Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  · have hxN : (⟨x, hxL⟩ : ↥Lhat) ∈ N := by
      rw [Subgroup.mem_comap]
      have hιx : ι ⟨x, hxL⟩ = x := Subtype.ext rfl
      rw [hιx]
      exact hxcenter
    rw [hNbot] at hxN
    have hx1 : (⟨x, hxL⟩ : ↥Lhat) = 1 := Subgroup.mem_bot.mp hxN
    have hval : (x : LGL 2 Mo.W) = 1 := by
      have h := congrArg Subtype.val hx1
      simpa using h
    exact Subtype.ext hval
  · exfalso
    have hab : ∀ a ∈ Mo.img V, ∀ b ∈ Mo.img (conjSubgroup V g), a * b = b * a := by
      intro a haV b hbW
      have haN : (⟨a, Mo.img_mono le_sup_left haV⟩ : ↥Lhat) ∈ N := by rw [hNtop]; trivial
      have hcenter : ι ⟨a, Mo.img_mono le_sup_left haV⟩ ∈ Subgroup.center ↥Khat := haN
      have hcomm := (Subgroup.mem_center_iff.mp hcenter) (ι ⟨b, Mo.img_mono le_sup_right hbW⟩)
      have h2 : (⟨b, Mo.img_mono le_sup_right hbW⟩ : ↥Lhat) *
          ⟨a, Mo.img_mono le_sup_left haV⟩ =
          ⟨a, Mo.img_mono le_sup_left haV⟩ * ⟨b, Mo.img_mono le_sup_right hbW⟩ := by
        apply Subgroup.inclusion_injective hLK
        simpa only [map_mul] using hcomm
      exact (Subtype.ext_iff.mp h2).symm
    exact not_comm_hat h1 h5 h15 hS c Mo hab

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
