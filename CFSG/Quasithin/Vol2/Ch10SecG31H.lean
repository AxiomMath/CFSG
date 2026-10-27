module

public import CFSG.Quasithin.Vol2.Ch10SecDTL
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.GroupTheory.GLnTwoSplitting CFSG.Open CFSG.Quasithin.ASInputs
open CFSG.Quasithin.Vol2.Ch10.SecD (mem_zpowers_iff_of_sq)

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

@[expose] def linAut (g : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V :=
  (MulEquiv.toAdditive g).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive g))

@[expose] def linAutHom : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := linAut
  map_one' := LinearEquiv.ext fun _ => rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => rfl

theorem linAutHom_apply (g : MulAut V) (w : Additive V) :
    linAutHom g w = Additive.ofMul (g (Additive.toMul w)) :=
  rfl

theorem linAutHom_injective : Function.Injective (linAutHom (V := V)) := by
  intro g h hgh
  ext v
  exact Additive.ofMul.injective (LinearEquiv.congr_fun hgh (Additive.ofMul v))

@[expose] def vecs (Δ : Set (Subgroup V)) : Set (Additive V) :=
  {w | Additive.toMul w ≠ 1 ∧ Subgroup.zpowers (Additive.toMul w) ∈ Δ}

@[expose] def forms (Gm : Subgroup (MulAut V)) (w : Additive V) :
    Submodule (ZMod 2) (Dual (ZMod 2) (Additive V)) where
  carrier := {φ | ∃ h : φ w = 0, LinearEquiv.transvection h ∈ Gm.map linAutHom}
  add_mem' := by
    rintro φ ψ ⟨hφ, hφm⟩ ⟨hψ, hψm⟩
    have h : (φ + ψ) w = 0 := by rw [LinearMap.add_apply, hφ, hψ, add_zero]
    refine ⟨h, ?_⟩
    rw [← transvection_mul_transvection_right hφ hψ h]
    exact Subgroup.mul_mem _ hφm hψm
  zero_mem' := ⟨rfl, by rw [transvection_zero_form]; exact Subgroup.one_mem _⟩
  smul_mem' := by
    rintro c φ ⟨hφ, hφm⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact ⟨rfl, by rw [transvection_zero_form]; exact Subgroup.one_mem _⟩
    · rw [one_smul]
      exact ⟨hφ, hφm⟩

theorem mem_forms {Gm : Subgroup (MulAut V)} {w : Additive V} {φ : Dual (ZMod 2) (Additive V)} :
    φ ∈ forms Gm w ↔ ∃ h : φ w = 0, LinearEquiv.transvection h ∈ Gm.map linAutHom :=
  Iff.rfl

omit [Module (ZMod 2) (Additive V)] in
theorem mem_transvGroup_iff {Gm : Subgroup (MulAut V)} {X : Subgroup V} {g : MulAut V} :
    g ∈ transvGroup Gm X ↔ g ∈ Gm ∧ ∀ v : V, g v * v⁻¹ ∈ X := by
  refine ⟨fun hg => ?_, fun h => Subgroup.subset_closure h⟩
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact ht
  | one => exact ⟨Gm.one_mem, fun v => by simp⟩
  | mul a b _ _ ha hb =>
    refine ⟨Gm.mul_mem ha.1 hb.1, fun v => ?_⟩
    have e : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact X.mul_mem (ha.2 _) (hb.2 _)
  | inv a _ ha =>
    refine ⟨Gm.inv_mem ha.1, fun v => ?_⟩
    have e : a⁻¹ v * v⁻¹ = (a (a⁻¹ v) * (a⁻¹ v)⁻¹)⁻¹ := by
      rw [MulAut.apply_inv_self]
      group
    rw [e]
    exact X.inv_mem (ha.2 _)

theorem exists_transvection_eq (hV : ∀ v : V, v ^ 2 = 1) {x : V} (hx : x ≠ 1) {g : MulAut V}
    (hg : ∀ v : V, g v * v⁻¹ ∈ Subgroup.zpowers x) :
    ∃ (φ : Dual (ZMod 2) (Additive V)) (h : φ (Additive.ofMul x) = 0),
      linAutHom g = LinearEquiv.transvection h := by
  have hx' : Additive.ofMul x ≠ 0 := by simpa using hx
  have hrange : ∀ w : Additive V,
      linAutHom g w - w ∈ Submodule.span (ZMod 2) {Additive.ofMul x} := by
    intro w
    rcases (mem_zpowers_iff_of_sq (hV x)).1 (hg (Additive.toMul w)) with h1 | h1
    · have : linAutHom g w - w = 0 := by
        rw [linAutHom_apply, sub_eq_zero]
        apply Additive.toMul.injective
        simpa [mul_inv_eq_one] using h1
      rw [this]
      exact Submodule.zero_mem _
    · have : linAutHom g w - w = Additive.ofMul x := by
        rw [linAutHom_apply]
        apply Additive.toMul.injective
        simpa [div_eq_mul_inv] using h1
      rw [this]
      exact Submodule.mem_span_singleton_self _
  set e := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive V) (Additive.ofMul x) hx'
  set δ : Additive V →ₗ[ZMod 2] Submodule.span (ZMod 2) {Additive.ofMul x} :=
    LinearMap.codRestrict _ ((linAutHom g : Additive V →ₗ[ZMod 2] Additive V) - LinearMap.id)
      hrange
  set φ : Dual (ZMod 2) (Additive V) := e.symm.toLinearMap ∘ₗ δ
  have hφ : ∀ w, φ w • Additive.ofMul x = linAutHom g w - w := by
    intro w
    have := e.apply_symm_apply (δ w)
    rw [LinearEquiv.toSpanNonzeroSingleton_apply] at this
    exact congrArg Subtype.val this
  have hφx : φ (Additive.ofMul x) = 0 := by
    rcases zmod_two_eq_zero_or_one (φ (Additive.ofMul x)) with h0 | h1
    · exact h0
    · exfalso
      have h2 := hφ (Additive.ofMul x)
      rw [h1, one_smul, eq_sub_iff_add_eq, two_add_self, linAutHom_apply] at h2
      apply hx
      have h3 : g x = 1 := by simpa using congrArg Additive.toMul h2.symm
      exact (MulEquiv.map_eq_one_iff g).1 h3
  refine ⟨φ, hφx, LinearEquiv.ext fun w => ?_⟩
  rw [transvection_apply, hφ w, add_sub_cancel]

theorem mem_zpowers_of_eq {x : V} {g : MulAut V} {φ : Dual (ZMod 2) (Additive V)}
    (h : φ (Additive.ofMul x) = 0) (hg : linAutHom g = LinearEquiv.transvection h) (v : V) :
    g v * v⁻¹ ∈ Subgroup.zpowers x := by
  have h1 := LinearEquiv.congr_fun hg (Additive.ofMul v)
  rw [linAutHom_apply, transvection_apply] at h1
  rcases zmod_two_eq_zero_or_one (φ (Additive.ofMul v)) with h0 | h0
  · rw [h0, zero_smul, add_zero] at h1
    rw [show g v = v from Additive.ofMul.injective h1, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [h0, one_smul] at h1
    rw [show g v = v * x from Additive.ofMul.injective h1, mul_comm v x, mul_assoc, mul_inv_cancel,
      mul_one]
    exact Subgroup.mem_zpowers x

theorem mem_transvGroup_zpowers_iff (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)}
    {x : V} (hx : x ≠ 1) {g : MulAut V} :
    g ∈ transvGroup Gm (Subgroup.zpowers x) ↔ g ∈ Gm ∧
      ∃ (φ : Dual (ZMod 2) (Additive V)) (h : φ (Additive.ofMul x) = 0),
        linAutHom g = LinearEquiv.transvection h := by
  rw [mem_transvGroup_iff]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, exists_transvection_eq hV hx h⟩
  · rintro ⟨hg, φ, h, he⟩
    exact ⟨hg, mem_zpowers_of_eq h he⟩

end CFSG.Quasithin.G31
