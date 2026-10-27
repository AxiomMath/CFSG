module

public import CFSG.Quasithin.Background.G2Omega4PlusModule

public section

namespace CFSG.Quasithin.S153P.PD

open scoped MatrixGroups
open CFSG.Quasithin.SL2Model

@[expose] def addEndOf {Γ Y : Type*} [Group Γ] [CommGroup Y] (ρ : Γ →* MulAut Y) :
    Γ →* AddMonoid.End (Additive Y) where
  toFun g := (MulEquiv.toAdditive (ρ g)).toAddMonoidHom
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (ρ 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' := fun g h => by
    apply AddMonoidHom.ext
    intro x
    show Additive.ofMul (ρ (g * h) (Additive.toMul x)) =
      Additive.ofMul (ρ g (ρ h (Additive.toMul x)))
    rw [map_mul]
    rfl

theorem sl2_rel_aux : ∀ a d : SL(2, ZMod 2),
    a * a ≠ 1 ∨ a = 1 ∨ d ^ 3 ≠ 1 ∨ d = 1 ∨ a * d⁻¹ * a * d = d⁻¹ := by
  decide +kernel

theorem sl2_c3_aux : ∀ c d : SL(2, ZMod 2),
    c ^ 3 ≠ 1 ∨ c = 1 ∨ d ^ 3 ≠ 1 ∨ d = 1 ∨ c = d ∨ c = d⁻¹ := by
  decide +kernel

theorem mul_natural_sum_of_fpf {Y : Type*} [CommGroup Y] [Finite Y] (h2 : ∀ y : Y, y * y = 1)
    (ρ : SL(2, ZMod 2) →* MulAut Y) (hfpf : ∀ y : Y, ρ (c3 (ZMod 2)) y = y → y = 1) :
    ∃ (s : ℕ) (e : Y ≃* Multiplicative (Fin s → Fin 2 → ZMod 2)),
      ∀ (A : SL(2, ZMod 2)) (y : Y),
        e (ρ A y) = Multiplicative.ofAdd (fun j => A • Multiplicative.toAdd (e y) j) := by
  obtain ⟨s, e, he⟩ := Om4Model.natural_sum_of_fpf (Y := Additive Y)
    (fun y => congrArg Additive.ofMul (h2 (Additive.toMul y))) (addEndOf ρ)
    (fun y hy => congrArg Additive.ofMul (hfpf (Additive.toMul y) (congrArg Additive.toMul hy)))
  refine ⟨s, AddEquiv.toMultiplicativeRight e, fun A y => ?_⟩
  exact congrArg Multiplicative.ofAdd (he A (Additive.ofMul y))

end CFSG.Quasithin.S153P.PD
