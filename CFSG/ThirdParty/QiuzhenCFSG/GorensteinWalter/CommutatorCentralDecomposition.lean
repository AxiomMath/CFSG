module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Commutators of central decompositions
-/

open scoped commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- If the `z`-parts of two decompositions centralize both `e`-parts and the
corresponding whole elements, their commutator is the commutator of the
`e`-parts. -/
public theorem commutator_eq_of_central_decomposition
    {G : Type u} [Group G]
    {z₁ z₂ e₁ e₂ x y : G}
    (hx : x = z₁ * e₁) (hy : y = z₂ * e₂)
    (hz₁e₁ : z₁ * e₁ = e₁ * z₁) (hz₁e₂ : z₁ * e₂ = e₂ * z₁)
    (hz₂e₁ : z₂ * e₁ = e₁ * z₂) (hz₂e₂ : z₂ * e₂ = e₂ * z₂)
    (hz₁y : z₁ * y = y * z₁) (hz₂x : z₂ * x = x * z₂) :
    ⁅x, y⁆ = ⁅e₁, e₂⁆ := by
  have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := by
    have h1 : z₁ * z₂ * e₂ = z₂ * z₁ * e₂ := by
      calc
        z₁ * z₂ * e₂ = z₁ * (z₂ * e₂) := by rw [mul_assoc]
        _ = (z₂ * e₂) * z₁ := by rw [hy] at hz₁y; exact hz₁y
        _ = z₂ * (e₂ * z₁) := by rw [mul_assoc]
        _ = z₂ * (z₁ * e₂) := by rw [hz₁e₂]
        _ = z₂ * z₁ * e₂ := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hz₂z₁ : z₂ * z₁ = z₁ * z₂ := by
    have h2 : z₂ * z₁ * e₁ = z₁ * z₂ * e₁ := by
      calc
        z₂ * z₁ * e₁ = z₂ * (z₁ * e₁) := by rw [mul_assoc]
        _ = (z₁ * e₁) * z₂ := by rw [hx] at hz₂x; exact hz₂x
        _ = z₁ * (e₁ * z₂) := by rw [mul_assoc]
        _ = z₁ * (z₂ * e₁) := by rw [hz₂e₁]
        _ = z₁ * z₂ * e₁ := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hz1_y : ⁅z₁, z₂ * e₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    calc
      z₁ * (z₂ * e₂) = (z₁ * z₂) * e₂ := by rw [mul_assoc]
      _ = (z₂ * z₁) * e₂ := by rw [hz₁z₂]
      _ = z₂ * (z₁ * e₂) := by rw [mul_assoc]
      _ = z₂ * (e₂ * z₁) := by rw [hz₁e₂]
      _ = (z₂ * e₂) * z₁ := by rw [mul_assoc]
  have hz2_e1 : ⁅e₁, z₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hz₂e₁.symm
  have hc₂e₁ : Commute z₂ e₁ := hz₂e₁
  have hc₂e₂ : Commute z₂ e₂ := hz₂e₂
  have hc₂c : Commute z₂ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) :=
    (((hc₂e₁.mul_right hc₂e₂).mul_right hc₂e₁.inv_right).mul_right
      hc₂e₂.inv_right)
  have hcomm1 : ⁅e₁, z₂ * e₂⁆ = ⁅e₁, e₂⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [hz2_e1, one_mul]
    rw [commutatorElement_def]
    rw [hc₂c.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hc₁e₁ : Commute z₁ e₁ := hz₁e₁
  have hc₁e₂ : Commute z₁ e₂ := hz₁e₂
  have hc₁c : Commute z₁ (e₁ * e₂ * e₁⁻¹ * e₂⁻¹) :=
    (((hc₁e₁.mul_right hc₁e₂).mul_right hc₁e₁.inv_right).mul_right
      hc₁e₂.inv_right)
  calc
    ⁅x, y⁆ = ⁅z₁ * e₁, z₂ * e₂⁆ := by rw [hx, hy]
    _ = z₁ * ⁅e₁, z₂ * e₂⁆ * z₁⁻¹ * ⁅z₁, z₂ * e₂⁆ :=
      commutatorElement_mul_left_eq_conj_mul z₁ e₁ (z₂ * e₂)
    _ = z₁ * ⁅e₁, e₂⁆ * z₁⁻¹ * 1 := by rw [hcomm1, hz1_y]
    _ = ⁅e₁, e₂⁆ := by
      rw [mul_one]
      rw [commutatorElement_def]
      rw [hc₁c.eq, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.GorensteinWalter
