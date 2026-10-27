module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SteinbergCEIsotypicMultiplicity
public import CFSG.LocalAnalysis.SteinbergCEMixedIrreducibleHead
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {G : Type*} [Group G] (W : Subgroup G) [IsElementaryAbelian 2 W]

@[expose] noncomputable def autLinear (a : MulAut ↥W) : Additive ↥W ≃ₗ[ZMod 2] Additive ↥W :=
  (MulEquiv.toAdditive a).toLinearEquiv fun c x => ZMod.map_smul (MulEquiv.toAdditive a) c x

@[expose] noncomputable def autGL : MulAut ↥W →* (Module.End (ZMod 2) (Additive ↥W))ˣ where
  toFun a := LinearMap.GeneralLinearGroup.ofLinearEquiv (autLinear W a)
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

@[expose] noncomputable def conjGL :
    ↥(normalizer (W : Set G)) →* (Module.End (ZMod 2) (Additive ↥W))ˣ :=
  (autGL W).comp W.normalizerMonoidHom

theorem conjGL_apply (n : ↥(normalizer (W : Set G))) (v : Additive ↥W) :
    ((Additive.toMul (((conjGL W n : (Module.End (ZMod 2) (Additive ↥W))ˣ) :
      Module.End (ZMod 2) (Additive ↥W)) v) : ↥W) : G) =
      n * ((Additive.toMul v : ↥W) : G) * (n : G)⁻¹ :=
  rfl

theorem conjGL_eq_one_iff (n : ↥(normalizer (W : Set G))) :
    conjGL W n = 1 ↔ (n : G) ∈ centralizer (W : Set G) := by
  rw [mem_centralizer_iff]
  constructor
  · intro h w hw
    have h1 := congrArg (fun g : (Module.End (ZMod 2) (Additive ↥W))ˣ =>
      ((Additive.toMul ((g : Module.End (ZMod 2) (Additive ↥W))
        (Additive.ofMul (⟨w, hw⟩ : ↥W))) : ↥W) : G)) h
    change (n : G) * w * (n : G)⁻¹ = w at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro h
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (n : G) * ((Additive.toMul v : ↥W) : G) * (n : G)⁻¹ = ((Additive.toMul v : ↥W) : G)
    rw [← h _ (Additive.toMul v).2, mul_inv_cancel_right]

theorem conjGL_mul_comm_iff (x y : ↥(normalizer (W : Set G))) :
    conjGL W x * conjGL W y = conjGL W y * conjGL W x ↔
      ⁅(x : G), (y : G)⁆ ∈ centralizer (W : Set G) := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, conjGL_eq_one_iff]
  rfl

theorem conjGL_apply_ne {n : ↥(normalizer (W : Set G))} {v : G} (hv : v ∈ W)
    (h : (n : G) * v ≠ v * n) :
    ((conjGL W n : (Module.End (ZMod 2) (Additive ↥W))ˣ) : Module.End (ZMod 2) (Additive ↥W))
      (Additive.ofMul ⟨v, hv⟩) ≠ Additive.ofMul ⟨v, hv⟩ := by
  intro h1
  apply h
  have h2 := congrArg (fun u : Additive ↥W => ((Additive.toMul u : ↥W) : G)) h1
  change (n : G) * v * (n : G)⁻¹ = v at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

@[expose] noncomputable def conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G)) :
    Subgroup (Module.End (ZMod 2) (Additive ↥W))ˣ :=
  ((conjGL W).comp (Subgroup.inclusion hE)).range

theorem conjGL_mem_conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G)) {e : G}
    (he : e ∈ E) : conjGL W ⟨e, hE he⟩ ∈ conjImage W hE :=
  ⟨⟨e, he⟩, rfl⟩

theorem mem_conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G))
    {g : (Module.End (ZMod 2) (Additive ↥W))ˣ} :
    g ∈ conjImage W hE ↔ ∃ e, ∃ he : e ∈ E, conjGL W ⟨e, hE he⟩ = g := by
  constructor
  · rintro ⟨⟨e, he⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact conjGL_mem_conjImage W hE he

theorem conjImage_comm {E F : Subgroup G} (hE : E ≤ normalizer (W : Set G))
    (hF : F ≤ normalizer (W : Set G))
    (h : ∀ e ∈ E, ∀ f ∈ F, ⁅e, f⁆ ∈ centralizer (W : Set G)) :
    ∀ x ∈ conjImage W hE, ∀ y ∈ conjImage W hF, x * y = y * x := by
  rintro _ ⟨⟨e, he⟩, rfl⟩ _ ⟨⟨f, hf⟩, rfl⟩
  exact (conjGL_mul_comm_iff W ⟨e, hE he⟩ ⟨f, hF hf⟩).mpr (h e he f hf)

theorem mem_fixedSub_conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G))
    (v : Additive ↥W) :
    v ∈ CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hE) ↔
      ((Additive.toMul v : ↥W) : G) ∈ centralizer (E : Set G) := by
  rw [CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub, mem_centralizer_iff]
  constructor
  · intro h e he
    have h1 := h _ (conjGL_mem_conjImage W hE he)
    have h2 := congrArg (fun u : Additive ↥W => ((Additive.toMul u : ↥W) : G)) h1
    change (e : G) * _ * e⁻¹ = _ at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  · rintro h _ ⟨⟨e, he⟩, rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (e : G) * ((Additive.toMul v : ↥W) : G) * (e : G)⁻¹ = ((Additive.toMul v : ↥W) : G)
    rw [h e he, mul_inv_cancel_right]

theorem card_fixedSub_conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G)) :
    Nat.card (CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hE)) =
      Nat.card ↥(W ⊓ centralizer (E : Set G)) :=
  Nat.card_congr
    { toFun := fun v => ⟨((Additive.toMul v.1 : ↥W) : G), (Additive.toMul v.1).2,
        (mem_fixedSub_conjImage W hE v.1).mp v.2⟩
      invFun := fun x => ⟨Additive.ofMul ⟨x.1, x.2.1⟩, (mem_fixedSub_conjImage W hE _).mpr x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_conjImage {E : Subgroup G} (hE : E ≤ normalizer (W : Set G)) :
    Nat.card (conjImage W hE) = (centralizer (W : Set G)).relIndex E := by
  rw [conjImage, ← Subgroup.index_ker, Subgroup.relIndex]
  congr 1
  ext e
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, conjGL_eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

theorem commutator_mem_commSpace {K : Subgroup G} (hK : K ≤ normalizer (W : Set G)) {v : G}
    (hv : v ∈ ⁅W, K⁆) :
    ∃ hvW : v ∈ W, Additive.ofMul (⟨v, hvW⟩ : ↥W) ∈
      CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hK) := by
  let S : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ W, Additive.ofMul (⟨g, hg⟩ : ↥W) ∈
        CFSG.LocalAnalysis.commSpace ⊤ (conjImage W hK)}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨ha, ha'⟩ := ha
        obtain ⟨hb, hb'⟩ := hb
        refine ⟨W.mul_mem ha hb, ?_⟩
        have e : Additive.ofMul (⟨a * b, W.mul_mem ha hb⟩ : ↥W) =
            Additive.ofMul ⟨a, ha⟩ + Additive.ofMul ⟨b, hb⟩ := rfl
        rw [e]
        exact Submodule.add_mem _ ha' hb'
      one_mem' := ⟨W.one_mem, Submodule.zero_mem _⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨ha, ha'⟩ := ha
        refine ⟨W.inv_mem ha, ?_⟩
        have e : Additive.ofMul (⟨a⁻¹, W.inv_mem ha⟩ : ↥W) = -Additive.ofMul ⟨a, ha⟩ := rfl
        rw [e]
        exact Submodule.neg_mem _ ha' }
  have hle : ⁅W, K⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro w hw k hk
    have hkw : k * w * k⁻¹ ∈ W := (mem_normalizer_iff.mp (hK hk) w).mp hw
    have hcw : ⁅w, k⁆ = w * (k * w * k⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    have hc : ⁅w, k⁆ ∈ W := by
      rw [hcw]
      exact W.mul_mem hw (W.inv_mem hkw)
    refine ⟨hc, ?_⟩
    have e : Additive.ofMul (⟨⁅w, k⁆, hc⟩ : ↥W) =
        -(((conjGL W ⟨k, hK hk⟩ : (Module.End (ZMod 2) (Additive ↥W))ˣ) :
          Module.End (ZMod 2) (Additive ↥W)) (Additive.ofMul ⟨w, hw⟩) -
            Additive.ofMul ⟨w, hw⟩) := by
      rw [neg_sub]
      change Additive.ofMul (⟨⁅w, k⁆, hc⟩ : ↥W) =
        Additive.ofMul ((⟨w, hw⟩ : ↥W) / ⟨k * w * k⁻¹, hkw⟩)
      congr 1
      apply Subtype.ext
      change ⁅w, k⁆ = w / (k * w * k⁻¹)
      rw [hcw, div_eq_mul_inv]
    rw [e]
    exact Submodule.neg_mem _ (CFSG.LocalAnalysis.sub_mem_commSpace
      (conjGL_mem_conjImage W hK hk) Submodule.mem_top)
  exact hle hv

theorem conjGL_mem_commutator {Y A : Subgroup G} (hY : Y ≤ normalizer (W : Set G))
    (hA : A ≤ normalizer (W : Set G)) {z : G} (hz : z ∈ ⁅Y, A⁆) :
    ∃ hzN : z ∈ normalizer (W : Set G),
      conjGL W ⟨z, hzN⟩ ∈ ⁅conjImage W hY, conjImage W hA⁆ := by
  let S : Subgroup G :=
    (⁅conjImage W hY, conjImage W hA⁆.comap (conjGL W)).map (normalizer (W : Set G)).subtype
  have hle : ⁅Y, A⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro y hy a ha
    refine ⟨⁅(⟨y, hY hy⟩ : ↥(normalizer (W : Set G))), ⟨a, hA ha⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (conjGL_mem_conjImage W hY hy)
      (conjGL_mem_conjImage W hA ha)
  obtain ⟨z', hz', rfl⟩ := hle hz
  exact ⟨z'.2, hz'⟩

theorem conjGL_mem_normalizer {Y : Subgroup G} (hY : Y ≤ normalizer (W : Set G))
    {a : ↥(normalizer (W : Set G))} (ha : ∀ y ∈ Y, (a : G) * y * (a : G)⁻¹ ∈ Y)
    (ha' : ∀ y ∈ Y, (a : G)⁻¹ * y * a ∈ Y) :
    conjGL W a ∈ normalizer (conjImage W hY : Set (Module.End (ZMod 2) (Additive ↥W))ˣ) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    refine ⟨⟨(a : G) * y * (a : G)⁻¹, ha y hy⟩, ?_⟩
    change conjGL W (a * ⟨y, hY hy⟩ * a⁻¹) =
      conjGL W a * conjGL W ⟨y, hY hy⟩ * (conjGL W a)⁻¹
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨⟨y, hy⟩, hy'⟩
    refine ⟨⟨(a : G)⁻¹ * y * a, ha' y hy⟩, ?_⟩
    change conjGL W (a⁻¹ * ⟨y, hY hy⟩ * a) = g
    rw [map_mul, map_mul, map_inv]
    rw [show conjGL W ⟨y, hY hy⟩ = conjGL W a * g * (conjGL W a)⁻¹ from hy']
    group

end CFSG.Quasithin.H13.NQBlock
