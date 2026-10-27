module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

variable {X : Type} [Group X] {W : Type} [Group W]

@[expose] def QuadPair (ρ : X →* MulAut W) (z β : X) : Prop :=
  ∀ w : W, ρ z (ρ β w) * (ρ β w)⁻¹ = ρ z w * w⁻¹

theorem quadPair_mul {ρ : X →* MulAut W} {z β β' : X} (h : QuadPair ρ z β)
    (h' : QuadPair ρ z β') : QuadPair ρ z (β * β') := by
  intro w
  rw [map_mul, MulAut.mul_apply, h (ρ β' w), h' w]

theorem quadPair_inv {ρ : X →* MulAut W} {z β : X} (h : QuadPair ρ z β) :
    QuadPair ρ z β⁻¹ := by
  intro w
  have e : ρ β (ρ β⁻¹ w) = w := by rw [map_inv, MulAut.apply_inv_self]
  have h1 := h (ρ β⁻¹ w)
  rw [e] at h1
  exact h1.symm

theorem quadPair_pow {ρ : X →* MulAut W} {z β : X} (h : QuadPair ρ z β) (n : ℕ) :
    QuadPair ρ z (β ^ n) := by
  induction n with
  | zero =>
    intro w
    rw [pow_zero, map_one, MulAut.one_apply]
  | succ n ih =>
    rw [pow_succ]
    exact quadPair_mul ih h

theorem quadPair_conj {ρ : X →* MulAut W} {z β h : X} (hβ : QuadPair ρ z β)
    (hz : h * z = z * h) : QuadPair ρ z (h * β * h⁻¹) := by
  intro w
  set w' := ρ h⁻¹ w with hw'
  have hw : ρ h w' = w := by rw [hw', map_inv, MulAut.apply_inv_self]
  have e1 : ρ (h * β * h⁻¹) w = ρ h (ρ β w') := by
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
  have e2 : ∀ u, ρ z (ρ h u) = ρ h (ρ z u) := fun u => by
    rw [← MulAut.mul_apply, ← map_mul, ← hz, map_mul, MulAut.mul_apply]
  rw [e1, e2, ← map_inv (ρ h), ← map_mul (ρ h), hβ w', map_mul (ρ h), map_inv (ρ h), ← e2, hw]

theorem quadPair_of_quad (hcomm : ∀ a b : W, a * b = b * a) {ρ : X →* MulAut W} {v v' : X}
    (h : ∀ w : W, ρ v (ρ v' w * w⁻¹) * (ρ v' w * w⁻¹)⁻¹ = 1) : QuadPair ρ v v' := by
  intro w
  have h1 := h w
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  calc ρ v (ρ v' w) * (ρ v' w)⁻¹ = ρ v (ρ v' w) * (ρ v w)⁻¹ * ρ v w * (ρ v' w)⁻¹ := by group
    _ = ρ v' w * w⁻¹ * ρ v w * (ρ v' w)⁻¹ := by rw [h1]
    _ = ρ v w * w⁻¹ := by
      rw [mul_assoc (ρ v' w), hcomm w⁻¹ (ρ v w), hcomm (ρ v' w) (ρ v w * w⁻¹),
        mul_inv_cancel_right]

theorem norm_eq_one_of_quadPair (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    {ρ : X →* MulAut W} {c : X} (h : QuadPair ρ (c * c) c) (w : W) :
    w * ρ c w * ρ (c * c) w * ρ (c * c * c) w = 1 := by
  have hinv : ∀ a : W, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hexp a)
  have h1 := h w
  have e : ρ (c * c) (ρ c w) = ρ (c * c * c) w := by rw [map_mul (ρ) (c * c) c, MulAut.mul_apply]
  rw [hinv, hinv, e] at h1
  calc w * ρ c w * ρ (c * c) w * ρ (c * c * c) w =
      ρ (c * c * c) w * ρ c w * (ρ (c * c) w * w) := by
        rw [hcomm (w * ρ c w * ρ (c * c) w), mul_assoc w (ρ c w), hcomm w (ρ c w * ρ (c * c) w),
          mul_assoc (ρ c w), ← mul_assoc (ρ (c * c * c) w)]
    _ = ρ (c * c) w * w * (ρ (c * c) w * w) := by rw [h1]
    _ = 1 := hexp _

end CFSG.Quasithin.Ch3E213M.OLB
