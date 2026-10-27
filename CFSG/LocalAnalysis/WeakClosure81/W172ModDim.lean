module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup

theorem w172_orderOf_two_dvd_finrank {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : LGL 2 U} (ht : t ^ p = 1)
    (hfix : ∀ u : U, t u = u → u = 0) : orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) U := by
  haveI : Fact p.Prime := Fact.mk hp
  haveI : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  refine CFSG.LinearAlgebra.CoprimeActions.PrimeCyclicFixedFreeDimension.orderOf_two_dvd_finrank
    p hp2 t ht ?_
  rw [LinearMap.ker_eq_bot']
  intro u hu
  apply hfix u
  have h0 : (t : U →ₗ[ZMod 2] U) u - u = 0 := by simpa using hu
  exact sub_eq_zero.mp h0

theorem w172_orderOf_two_dvd_finrank_sub {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : LGL 2 W} (hy : y ^ p = 1)
    (M : Submodule (ZMod 2) W) (hyM : ∀ x ∈ M, y x ∈ M) (hfix : ∀ x ∈ M, y x = x → x = 0) :
    orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) ↥M := by
  haveI : Finite ↥M := inferInstance
  have hpowmem : ∀ n : ℕ, ∀ x ∈ M, (y ^ n) x ∈ M := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', LinearEquiv.mul_apply]
      exact hyM _ (ih x hx)
  have hmap : M.map (y : W →ₗ[ZMod 2] W) = M := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hyM x hx
    · intro x hx
      refine ⟨(y ^ (p - 1)) x, hpowmem (p - 1) x hx, ?_⟩
      have h1 : (y * y ^ (p - 1)) x = x := by
        rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hy]
        rfl
      rwa [LinearEquiv.mul_apply] at h1
  let e : ↥M ≃ₗ[ZMod 2] ↥M := LinearEquiv.ofSubmodules y M M hmap
  have he : ∀ w : ↥M, ((e w : ↥M) : W) = y (w : W) := fun w => rfl
  have hpowe : ∀ n : ℕ, ∀ w : ↥M, (((e ^ n) w : ↥M) : W) = (y ^ n) (w : W) := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply, he, ih]
  have hep : e ^ p = 1 := by
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [hpowe p w, hy]
    rfl
  have hfixe : ∀ w : ↥M, e w = w → w = 0 := by
    intro w hw
    apply Subtype.ext
    refine hfix (w : W) w.2 ?_
    have h1 := congrArg Subtype.val hw
    rw [he] at h1
    exact h1
  exact w172_orderOf_two_dvd_finrank hp hp2 hep hfixe

end CFSG.LocalAnalysis.WeakClosure81

end
