module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3Unitri
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

section Coef

variable {H : Type*} [Group H]

@[expose] def piAct {ι V₀ : Type*} [AddCommGroup V₀] (e : H →* AddMonoid.End V₀) :
    H →* AddMonoid.End (ι → V₀) where
  toFun g :=
    { toFun := fun x i => e g (x i)
      map_zero' := funext fun i => map_zero _
      map_add' := fun x y => funext fun i => map_add _ _ _ }
  map_one' := AddMonoidHom.ext fun x => funext fun i => by
    show e 1 (x i) = x i
    rw [map_one]
    rfl
  map_mul' g h := AddMonoidHom.ext fun x => funext fun i => by
    show e (g * h) (x i) = e g (e h (x i))
    rw [map_mul]
    rfl

@[simp] theorem piAct_apply {ι V₀ : Type*} [AddCommGroup V₀] (e : H →* AddMonoid.End V₀)
    (g : H) (x : ι → V₀) (i : ι) : piAct e g x i = e g (x i) := rfl

variable {N : Type*} [AddCommGroup N] {Q : Type*} [AddCommGroup Q]

@[expose] def homAct (ρ : H →* AddMonoid.End N) : H →* AddMonoid.End (N →+ Q) where
  toFun g :=
    { toFun := fun φ => φ.comp (ρ g⁻¹)
      map_zero' := AddMonoidHom.ext fun _ => rfl
      map_add' := fun _ _ => AddMonoidHom.ext fun _ => rfl }
  map_one' := AddMonoidHom.ext fun φ => AddMonoidHom.ext fun x => by
    show φ (ρ 1⁻¹ x) = φ x
    rw [inv_one, map_one]
    rfl
  map_mul' g h := AddMonoidHom.ext fun φ => AddMonoidHom.ext fun x => by
    show φ ((ρ (g * h)⁻¹) x) = φ ((ρ h⁻¹) ((ρ g⁻¹) x))
    rw [mul_inv_rev, map_mul]
    rfl

@[simp] theorem homAct_apply (ρ : H →* AddMonoid.End N) (g : H) (φ : N →+ Q) (x : N) :
    homAct ρ g φ x = φ (ρ g⁻¹ x) := rfl

theorem homAct_fixed_free [Finite N] (ρ : H →* AddMonoid.End N) (s : H)
    (hs : ∀ x : N, ρ s x = x → x = 0) (φ : N →+ Q) (hφ : homAct ρ s φ = φ) : φ = 0 := by
  have hs' : ∀ x : N, ρ s⁻¹ x = x → x = 0 := by
    intro x hx
    apply hs
    have h1 : ρ (s * s⁻¹) x = x := by
      rw [mul_inv_cancel, map_one]
      rfl
    have h2 : ρ (s * s⁻¹) x = ρ s (ρ s⁻¹ x) := by
      rw [map_mul]
      rfl
    rw [hx] at h2
    exact h2.symm.trans h1
  have hT : Function.Injective (fun x : N => ρ s⁻¹ x - x) := by
    intro x y hxy
    have h2 : ρ s⁻¹ (x - y) - (x - y) = 0 := by
      calc ρ s⁻¹ (x - y) - (x - y) = (ρ s⁻¹ x - x) - (ρ s⁻¹ y - y) := by
            rw [map_sub]
            abel
        _ = 0 := sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (hs' _ (sub_eq_zero.mp h2))
  have hsurj : Function.Surjective (fun x : N => ρ s⁻¹ x - x) :=
    Finite.surjective_of_injective hT
  have hc : ∀ z : N, φ (ρ s⁻¹ z) = φ z := fun z => by
    have := congrArg (fun ψ : N →+ Q => ψ z) hφ
    exact this
  refine AddMonoidHom.ext fun y => ?_
  obtain ⟨x, hx⟩ := hsurj y
  show φ y = 0
  rw [← hx, map_sub, hc, sub_self]

end Coef

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
