module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB5

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

variable {X : Type} [Group X] {W : Type} [Group W]

@[expose] def tri (ρ : X →* MulAut W) (x : X) (w : W) : W := w * ρ x w * ρ (x * x) w

theorem rho_rho (ρ : X →* MulAut W) (g h : X) (w : W) : ρ g (ρ h w) = ρ (g * h) w := by
  rw [map_mul, MulAut.mul_apply]

theorem nine (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    (t00 t01 t02 t10 t11 t12 t20 t21 t22 : W) :
    t00 = t00 * t01 * t02 * (t10 * t11 * t12) * (t20 * t21 * t22) * (t00 * t10 * t20) *
      (t00 * t01 * t02) * (t00 * t11 * t22) * (t00 * t12 * t21) := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have hexp' : ∀ a b : W, a * (a * b) = b := fun a b => by rw [← mul_assoc, hexp, one_mul]
  simp only [mul_comm, mul_left_comm, hexp, hexp', mul_one]

theorem tri_mul (hcomm : ∀ a b : W, a * b = b * a) (ρ : X →* MulAut W) (x : X) (w₁ w₂ : W) :
    tri ρ x (w₁ * w₂) = tri ρ x w₁ * tri ρ x w₂ := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  simp only [tri, map_mul (ρ x), map_mul (ρ (x * x))]
  simp only [mul_assoc, mul_comm, mul_left_comm]

theorem tri_fixed (hcomm : ∀ a b : W, a * b = b * a) (ρ : X →* MulAut W) {x : X}
    (hx3 : x * x * x = 1) (w : W) : ρ x (tri ρ x w) = tri ρ x w := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have e : x * (x * x) = 1 := by rw [← mul_assoc, hx3]
  simp only [tri, map_mul (ρ x), rho_rho, e, map_one, MulAut.one_apply]
  simp only [mul_comm, mul_left_comm]

theorem tri_conj (ρ : X →* MulAut W) (x y : X) (w : W) :
    tri ρ x (ρ y w) = ρ y (tri ρ (y⁻¹ * x * y) w) := by
  have g1 : y * (y⁻¹ * x * y) = x * y := by group
  have g2 : y * (y⁻¹ * x * y * (y⁻¹ * x * y)) = x * x * y := by group
  simp only [tri, map_mul (ρ y), rho_rho, g1, g2]

theorem tri_inv (hcomm : ∀ a b : W, a * b = b * a) (ρ : X →* MulAut W) {x : X}
    (hx3 : x * x * x = 1) (w : W) : tri ρ x⁻¹ w = tri ρ x w := by
  have h1 : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx3])
  have h2 : x⁻¹ * x⁻¹ = x := by rw [h1, ← mul_assoc, hx3, one_mul]
  simp only [tri, h2]
  rw [h1, mul_assoc w, hcomm (ρ (x * x) w), ← mul_assoc]

theorem tri_of_fixed (hexp : ∀ a : W, a * a = 1) (ρ : X →* MulAut W) {x : X} {w : W}
    (h : ρ x w = w) : tri ρ x w = w := by
  have h2 : ρ (x * x) w = w := by rw [← rho_rho, h, h]
  rw [tri, h, h2, hexp, one_mul]

theorem tri_decomp (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    (ρ : X →* MulAut W) (x : X) (w : W) : w = tri ρ x w * (ρ x w * ρ (x * x) w) := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  simp only [tri, mul_comm, mul_left_comm, hexp, mul_one]

theorem tri_compl (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    (ρ : X →* MulAut W) {x : X} (hx3 : x * x * x = 1) (w : W) :
    tri ρ x (ρ x w * ρ (x * x) w) = 1 := by
  let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
  have e3 : x * x * x = 1 := hx3
  have e4 : x * (x * x) = 1 := by rw [← mul_assoc, hx3]
  have e5 : x * x * (x * x) = x := by
    rw [← mul_assoc, hx3, one_mul]
  simp only [tri, map_mul (ρ x), map_mul (ρ (x * x)), rho_rho, e3, e4, e5, map_one,
    MulAut.one_apply]
  simp only [mul_comm, mul_left_comm, hexp, mul_one]

end CFSG.Quasithin.Ch3E213M.OLB
