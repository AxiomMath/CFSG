module

public import CFSG.Quasithin.EmptyFaithful.S153PDa

public section

namespace CFSG.Quasithin.S153P.PD

open scoped MatrixGroups

section Core

variable {V : Type*} [AddCommGroup V]

theorem fpf_core (h2 : ∀ v : V, v + v = 0)
    (ρ : SL(2, ZMod 2) →* AddMonoid.End V) (a d : SL(2, ZMod 2))
    (hrel : a * d⁻¹ * a * d = d⁻¹) (Fb Xb : AddSubgroup V)
    (hFX : ∀ v ∈ Fb, v ∈ Xb → v = 0)
    (hprod : ∀ v : V, ∃ f ∈ Fb, ∃ x ∈ Xb, v = f + x)
    (hα1 : ∀ f ∈ Fb, ρ a f = f) (hα2 : ∀ v : V, ρ a v + v ∈ Fb)
    (hδ1 : ∀ x ∈ Xb, ρ d x ∈ Fb) (hδ2 : ∀ f ∈ Fb, ρ d⁻¹ f ∈ Xb) :
    ∀ m : V, ρ d m = m → m = 0 := by
  have hδε : ∀ v, ρ d (ρ d⁻¹ v) = v := fun v => by
    rw [← Om4Model.rep_mul_apply, mul_inv_cancel, Om4Model.rep_one_apply]
  have hεδ : ∀ v, ρ d⁻¹ (ρ d v) = v := fun v => by
    rw [← Om4Model.rep_mul_apply, inv_mul_cancel, Om4Model.rep_one_apply]
  have hr : ∀ v, ρ a (ρ d⁻¹ (ρ a (ρ d v))) = ρ d⁻¹ v := fun v => by
    have := congrArg (fun A => ρ A v) hrel
    simpa only [Om4Model.rep_mul_apply] using this
  intro m hm
  have hεm : ρ d⁻¹ m = m := by
    have := hεδ m
    rwa [hm] at this
  obtain ⟨u₁, hu₁def⟩ : ∃ u₁, u₁ = ρ a m + m := ⟨_, rfl⟩
  have hu₁ : u₁ ∈ Fb := hu₁def ▸ hα2 m
  have hαm : ρ a m = u₁ + m := by
    rw [hu₁def]
    linear_combination (norm := abel1) -(h2 m)
  obtain ⟨u₂, hu₂def⟩ : ∃ u₂, u₂ = ρ d⁻¹ u₁ := ⟨_, rfl⟩
  have hu₂ : u₂ ∈ Xb := hu₂def ▸ hδ2 u₁ hu₁
  have hεαm : ρ d⁻¹ (ρ a m) = u₂ + m := by
    rw [hαm, map_add, hεm, hu₂def]
  have hE : ρ a u₂ + (u₁ + m) = m := by
    have := hr m
    rw [hm, hεαm, map_add, hαm, hεm] at this
    exact this
  have hαu₂ : ρ a u₂ = u₁ := by
    linear_combination (norm := abel1) hE - (h2 u₁)
  have hu₂F : u₂ ∈ Fb := by
    have h1 := hα2 u₂
    rw [hαu₂] at h1
    have h3 := Fb.add_mem hu₁ h1
    have : u₁ + (u₁ + u₂) = u₂ := by
      linear_combination (norm := abel1) (h2 u₁)
    rwa [this] at h3
  have hu₂0 : u₂ = 0 := hFX u₂ hu₂F hu₂
  have hu₁0 : u₁ = 0 := by
    rw [← hαu₂, hu₂0, map_zero]
  have hαm' : ρ a m = m := by
    rw [hu₁0, zero_add] at hαm
    exact hαm
  obtain ⟨f, hf, x, hx, hfx⟩ := hprod m
  have hαx : ρ a x = x := by
    have h1 := hαm'
    rw [hfx, map_add, hα1 f hf] at h1
    linear_combination (norm := abel1) h1
  have hεx : ρ d⁻¹ x = x := by
    have h1 := hr x
    have h2' := hα1 _ (hδ1 x hx)
    rw [h2', hεδ, hαx] at h1
    exact h1.symm
  have hδx : ρ d x = x := by
    have := hδε x
    rwa [hεx] at this
  have hxF : x ∈ Fb := by
    have := hδ1 x hx
    rwa [hδx] at this
  have hx0 : x = 0 := hFX x hxF hx
  have hmf : m = f := by rw [hfx, hx0, add_zero]
  have hmX : m ∈ Xb := by
    have := hδ2 m (hmf ▸ hf)
    rwa [hεm] at this
  exact hFX m (hmf ▸ hf) hmX

end Core

theorem fpf_mul {Y : Type*} [CommGroup Y] (h2 : ∀ y : Y, y * y = 1)
    (ρ : SL(2, ZMod 2) →* MulAut Y) (a d : SL(2, ZMod 2)) (hrel : a * d⁻¹ * a * d = d⁻¹)
    (Fb Xb : Subgroup Y)
    (hFX : ∀ y ∈ Fb, y ∈ Xb → y = 1)
    (hprod : ∀ y : Y, ∃ f ∈ Fb, ∃ x ∈ Xb, y = f * x)
    (hα1 : ∀ f ∈ Fb, ρ a f = f) (hα2 : ∀ y : Y, ρ a y * y⁻¹ ∈ Fb)
    (hδ1 : ∀ x ∈ Xb, ρ d x ∈ Fb) (hδ2 : ∀ f ∈ Fb, ρ d⁻¹ f ∈ Xb) :
    ∀ m : Y, ρ d m = m → m = 1 := by
  intro m hm
  have key := fpf_core (V := Additive Y)
    (fun v => congrArg Additive.ofMul (h2 (Additive.toMul v))) (addEndOf ρ) a d hrel
    (Subgroup.toAddSubgroup Fb) (Subgroup.toAddSubgroup Xb)
    (fun v hv hv' => congrArg Additive.ofMul (hFX (Additive.toMul v) hv hv'))
    (fun v => by
      obtain ⟨f, hf, x, hx, h⟩ := hprod (Additive.toMul v)
      exact ⟨Additive.ofMul f, hf, Additive.ofMul x, hx, congrArg Additive.ofMul h⟩)
    (fun f hf => congrArg Additive.ofMul (hα1 (Additive.toMul f) hf))
    (fun v => by
      have := hα2 (Additive.toMul v)
      rwa [inv_eq_of_mul_eq_one_right (h2 (Additive.toMul v))] at this)
    (fun x hx => hδ1 (Additive.toMul x) hx)
    (fun f hf => hδ2 (Additive.toMul f) hf)
    (Additive.ofMul m) (congrArg Additive.ofMul hm)
  exact congrArg Additive.toMul key

end CFSG.Quasithin.S153P.PD
