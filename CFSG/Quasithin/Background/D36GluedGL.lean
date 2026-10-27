module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin

theorem exists_injective_GL_of_mulAut {G A : Type} [Group G] [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ 2 = 1) (φ : G →* MulAut A) (hφ : Function.Injective φ) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin (rk A)) (ZMod 2), Function.Injective ρ := by
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hA _
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  have hfin : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (Additive A) = rk A := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod] at h
    have hcard : Nat.card A = 2 ^ rk A :=
      card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hA)
    have hV' : Nat.card (Additive A) = 2 ^ rk A := hcard
    rw [hV'] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b : Module.Basis (Fin (rk A)) (ZMod 2) (Additive A) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim
  let act : G → (Additive A →+ Additive A) := fun g =>
    MonoidHom.toAdditive (φ g).toMonoidHom
  let f : G →* Module.End (ZMod 2) (Additive A) :=
    { toFun := fun g => AddMonoidHom.toZModLinearMap 2 (act g)
      map_one' := LinearMap.ext fun x => by
        show Additive.ofMul ((φ 1) (Additive.toMul x)) = x
        rw [map_one]
        rfl
      map_mul' := fun g₁ g₂ => LinearMap.ext fun x => by
        show Additive.ofMul ((φ (g₁ * g₂)) (Additive.toMul x)) =
          Additive.ofMul ((φ g₁) ((φ g₂) (Additive.toMul x)))
        rw [map_mul]
        rfl }
  have hf1 : ∀ g : G, f g = 1 → g = 1 := by
    intro g hg
    apply hφ
    rw [map_one]
    refine MulEquiv.ext fun a => ?_
    have := congrArg (fun T => Additive.toMul (T (Additive.ofMul a))) hg
    simpa [f, act] using this
  let ρ : G →* Matrix.GeneralLinearGroup (Fin (rk A)) (ZMod 2) :=
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).toMonoidHom.comp
      f.toHomUnits
  refine ⟨ρ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : f.toHomUnits g = 1 := by
    have : (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)
        (f.toHomUnits g) =
        (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv) 1 := by
      rw [map_one]
      exact hg
    exact (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv).injective this
  exact hf1 g (congrArg Units.val h1)

end CFSG.Quasithin
