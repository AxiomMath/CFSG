module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2HatK
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Img
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2OrbitHyp
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeE
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.LocalAnalysis.WeakClosure81.W19Min
public import CFSG.Open.SplitBNPair
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Defs

variable {H E : Subgroup G} (Mo : ModDataE H E)

@[expose] def hatGamma (V : Subgroup G) : Set (Subgroup (LGL 2 Mo.W)) :=
  {A | ∃ h ∈ H, A = Mo.img (conjSubgroup V h)}

@[expose] noncomputable def hatVA (V₀ V : Subgroup G) (A : Subgroup (LGL 2 Mo.W)) :
    Submodule (ZMod 2) Mo.W :=
  ⨆ h : {h : G // h ∈ H ∧ Mo.img (conjSubgroup V h) = A}, Mo.sp (conjSubgroup V₀ h.1)

@[expose] noncomputable def hatV1 (V₀ V : Subgroup G) : Subgroup (VG (Mo.img H)) :=
  UAOf (Mo.img H) (hatVA Mo V₀ V) (Mo.img V)

end Defs

theorem hatGamma_transitive {H E : Subgroup G} (Mo : ModDataE H E) (V : Subgroup G)
    (hV : V ≤ H) :
    ∀ A ∈ hatGamma Mo V, ∀ B ∈ hatGamma Mo V, ∃ g ∈ Mo.img H, B = cj g A := by
  rintro A ⟨h, hh, rfl⟩ B ⟨h', hh', rfl⟩
  have hAh : conjSubgroup V h ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = h⁻¹ * (h * z * h⁻¹) * h := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hV hz)) hh
  refine ⟨Mo.ρ ⟨h'⁻¹ * h, H.mul_mem (H.inv_mem hh') hh⟩,
    Mo.mem_img.2 ⟨⟨h'⁻¹ * h, H.mul_mem (H.inv_mem hh') hh⟩,
      H.mul_mem (H.inv_mem hh') hh, rfl⟩, ?_⟩
  rw [Mo.img_conj hAh]
  congr 1
  rw [conjSubgroup_conjSubgroup]
  congr 1
  group

theorem kHatOf_hatGamma_eq {H E : Subgroup G} (Mo : ModDataE H E) (V : Subgroup G)
    (hV : V ≤ H) : kHatOf (hatGamma Mo V) = Mo.img (conjClosure V H) := by
  have hclH : conjClosure V H ≤ H :=
    conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hV hz)) (H.inv_mem hh)
  refine le_antisymm ?_ ?_
  · rw [kHatOf, Subgroup.closure_le]
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨A, hx'⟩
    rcases Set.mem_iUnion.1 hx' with ⟨hA, hxA⟩
    obtain ⟨h, hh, rfl⟩ := hA
    refine Mo.img_mono (fun z hz => ?_) hxA
    rw [mem_conjSubgroup_iff] at hz
    have hgen := mem_conjClosure (H.inv_mem hh) hz
    have e : h⁻¹ * (h * z * h⁻¹) * h⁻¹⁻¹ = z := by group
    rwa [e] at hgen
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Mo.mem_img.1 hr
    have key : ∀ y ∈ conjClosure V H, ∀ (hy : y ∈ H),
        Mo.ρ ⟨y, hy⟩ ∈ kHatOf (hatGamma Mo V) := by
      intro y hy
      refine Subgroup.closure_induction
        (p := fun y _ => ∀ hy : y ∈ H, Mo.ρ ⟨y, hy⟩ ∈ kHatOf (hatGamma Mo V))
        ?_ ?_ ?_ ?_ hy
      · rintro y ⟨h, hh, z, hz, rfl⟩ hy'
        refine Subgroup.subset_closure (Set.mem_iUnion.2
          ⟨Mo.img (conjSubgroup V h⁻¹),
            Set.mem_iUnion.2 ⟨⟨h⁻¹, H.inv_mem hh, rfl⟩, ?_⟩⟩)
        refine Mo.mem_img.2 ⟨⟨h * z * h⁻¹, hy'⟩, ?_, rfl⟩
        rw [mem_conjSubgroup_iff]
        have e : h⁻¹ * (h * z * h⁻¹) * (h⁻¹)⁻¹ = z := by group
        rwa [e]
      · intro hy'
        have e : (⟨1, hy'⟩ : ↥H) = 1 := Subtype.ext rfl
        rw [e, map_one]
        exact (kHatOf (hatGamma Mo V)).one_mem
      · intro x y hx hy ihx ihy hxy'
        have e : (⟨x * y, hxy'⟩ : ↥H) = ⟨x, hclH hx⟩ * ⟨y, hclH hy⟩ := Subtype.ext rfl
        rw [e, map_mul]
        exact (kHatOf (hatGamma Mo V)).mul_mem (ihx (hclH hx)) (ihy (hclH hy))
      · intro x hx ihx hx'
        have e : (⟨x⁻¹, hx'⟩ : ↥H) = (⟨x, hclH hx⟩)⁻¹ := Subtype.ext rfl
        rw [e, map_inv]
        exact (kHatOf (hatGamma Mo V)).inv_mem (ihx (hclH hx))
    simpa using key (j : G) hj j.2

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem img_conjSubgroup_eq_iff (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    Mo.img (conjSubgroup V x) = Mo.img (conjSubgroup V y) ↔ x * y⁻¹ ∈ M := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVxH : conjSubgroup V x ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) (hVH hz)) hx
  have hVyH : conjSubgroup V y ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = y⁻¹ * (y * z * y⁻¹) * y := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hy) (hVH hz)) hy
  constructor
  · intro heq
    have hle : conjSubgroup V x ≤
        conjSubgroup V y ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :=
      (Mo.img_le_img_iff hVxH hVyH).1 heq.le
    have hCy : conjSubgroup (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) y⁻¹ =
        H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H (H.inv_mem hy)),
        conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H := H) (H.inv_mem hy))]
    have hconj : conjSubgroup (conjSubgroup V x) y⁻¹ ≤
        V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
      calc conjSubgroup (conjSubgroup V x) y⁻¹
          ≤ conjSubgroup (conjSubgroup V y ⊔
              (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) y⁻¹ :=
            E3.conjSubgroup_mono_left y⁻¹ hle
        _ = conjSubgroup (conjSubgroup V y) y⁻¹ ⊔
              conjSubgroup (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) y⁻¹ :=
            Subgroup.map_sup _ _ _
        _ = V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) := by
            rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one, hCy]
    rw [conjSubgroup_conjSubgroup] at hconj
    exact (conjSubgroup_le_sup_iff h1 h5 h15 hS c (y := x * y⁻¹)
      (H.mul_mem hx (H.inv_mem hy))).1 hconj
  · intro hm
    have hVnorm : x * y⁻¹ ∈ normalizer (V : Set G) := by
      rw [c.cex.hyp.h6.normalizer_eq]
      exact hm
    have hconjV : conjSubgroup V (x * y⁻¹) = V :=
      conjSubgroup_eq_iff_mem_normalizer.2 hVnorm
    have h1 : conjSubgroup (conjSubgroup V (x * y⁻¹)) y = conjSubgroup V x := by
      rw [conjSubgroup_conjSubgroup]
      congr 1
      group
    have h2 : conjSubgroup (conjSubgroup V (x * y⁻¹)) y = conjSubgroup V y := by rw [hconjV]
    exact congrArg Mo.img (h1.symm.trans h2)

theorem hatVA_img_conj (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {x : G}
    (hx : x ∈ H) :
    hatVA Mo V₀ V (Mo.img (conjSubgroup V x)) = Mo.sp (conjSubgroup V₀ x) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨h, hh, himg⟩
    have hM : h * x⁻¹ ∈ M :=
      (img_conjSubgroup_eq_iff h1 h5 h15 hS c Mo hh hx).1 himg
    have hnorm : h * x⁻¹ ∈ normalizer (V₀ : Set G) := by
      rw [c.cex.hyp.normalizer₀]
      exact hM
    have hconj : conjSubgroup V₀ h = conjSubgroup V₀ x := by
      have e : conjSubgroup V₀ h = conjSubgroup (conjSubgroup V₀ (h * x⁻¹)) x := by
        rw [conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [e, conjSubgroup_eq_iff_mem_normalizer.2 hnorm]
    exact le_of_eq (congrArg Mo.sp hconj)
  · exact le_iSup (fun h : {h : G // h ∈ H ∧
      Mo.img (conjSubgroup V h) = Mo.img (conjSubgroup V x)} => Mo.sp (conjSubgroup V₀ h.1))
      ⟨x, hx, rfl⟩

theorem card_img_conjSubgroup (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {x : G} (hx : x ∈ H) :
    Nat.card (Mo.img (conjSubgroup V x)) = 2 ^ E3.mQuot V (U ⊔ V₀) := by
  have hVH : V ≤ H := c.cex.V_le_S.trans (c.S_le.trans c.mem.1)
  have hVxH : conjSubgroup V x ≤ H := by
    intro z hz
    rw [mem_conjSubgroup_iff] at hz
    have e : z = x⁻¹ * (x * z * x⁻¹) * x := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) (hVH hz)) hx
  have hinfx : conjSubgroup V x ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) =
      conjSubgroup (U ⊔ V₀) x := by
    have hbase := c.cex.inf_centralizer_conjClosure_eq h1 h5 h15 hS c.mem
    have h := congrArg (fun A : Subgroup G => conjSubgroup A x) hbase
    rwa [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (le_normalizer_conjClosure (U ⊔ V₀) H hx)] at h
  rw [Mo.card_img hVxH, ← Subgroup.inf_relIndex_left (H := conjSubgroup V x)
      (K := centralizer (conjClosure (U ⊔ V₀) H : Set G)),
    hinfx, E3.relIndex_conjSubgroup, E3.relIndex_eq_two_pow c.cex.hyp.isPGroup (U ⊔ V₀)]

theorem sp_conjSubgroup_inf_eq_bot (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {x y : G} (hxy : x * y⁻¹ ∉ M) :
    Mo.sp (conjSubgroup V₀ x) ⊓ Mo.sp (conjSubgroup V₀ y) = ⊥ := by
  have hbot : conjSubgroup V₀ (x * y⁻¹) ⊓ V₀ = ⊥ := c.cex.hyp.conj_inf_eq_bot hxy
  have h1 : conjSubgroup (conjSubgroup V₀ x ⊓ conjSubgroup V₀ y) y⁻¹ = ⊥ := by
    rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      mul_inv_cancel, conjSubgroup_one, hbot]
  have h2 : conjSubgroup V₀ x ⊓ conjSubgroup V₀ y = ⊥ := by
    have h := congrArg (fun A : Subgroup G => conjSubgroup A y) h1
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, E3.conjSubgroup_bot] at h
  rw [← Mo.sp_inf, h2]
  exact Mo.sp_eq_bot_iff.2 (by simp)

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
