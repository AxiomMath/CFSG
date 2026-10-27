module

public import CFSG.Permutation.FiveTransitive.ConjugateMinimalOrbit

public section

namespace CFSG

namespace FiveTransitive.EquivariantSemiregular

open MulAction

theorem free_of_equivariant
    (Q R X Y : Type*) [Group Q] [Group R] [MulAction Q X] [MulAction R Y]
    (φ : Q ≃* R) (e : X ≃ Y)
    (he : ∀ (q : Q) (x : X), e (q • x) = φ q • e x)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1) :
    ∀ (r : R) (y : Y), y ∉ fixedPoints R Y → r • y = y → r = 1 := by
  intro r y hy hry
  have hx : e.symm y ∉ fixedPoints Q X := by
    intro h
    have h' := (ConjugateMinimalOrbit.fixedPoints_equivariant φ e he (e.symm y)).mp h
    exact hy (by simpa only [e.apply_symm_apply] using h')
  have hqx : φ.symm r • e.symm y = e.symm y := by
    apply e.injective
    rw [he, φ.apply_symm_apply, e.apply_symm_apply, hry]
  have h1 := hfree (φ.symm r) (e.symm y) hx hqx
  simpa only [φ.apply_symm_apply, map_one] using congrArg φ h1

theorem square_and_commute_of_equiv
    (Q R : Type*) [Group Q] [Group R] (φ : Q ≃* R)
    (hsq : ∀ q : Q, q * q = 1) (hcomm : ∀ q r : Q, q * r = r * q) :
    (∀ r : R, r * r = 1) ∧ (∀ r t : R, r * t = t * r) := by
  constructor
  · intro r
    simpa only [map_mul, map_one, φ.apply_symm_apply] using congrArg φ (hsq (φ.symm r))
  · intro r t
    simpa only [map_mul, φ.apply_symm_apply] using congrArg φ (hcomm (φ.symm r) (φ.symm t))

end FiveTransitive.EquivariantSemiregular

end CFSG
