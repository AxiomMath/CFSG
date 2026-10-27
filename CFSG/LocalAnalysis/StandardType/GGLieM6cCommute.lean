module

public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.StandardType.LieCore.M6c

theorem commute_of_lift_inverts_center {G H : Type*} [Group G] [Group H] (π : G →* H)
    (hπ : π.ker ≤ Subgroup.center G) (hexp : ∀ z ∈ π.ker, z ^ 3 = 1) (Ft : G →* G) (F : H →* H)
    (hF : ∀ g, π (Ft g) = F (π g)) (hinv : ∀ z ∈ π.ker, Ft z = z⁻¹) {x y : G}
    (hx : F (π x) = π x) (hy : F (π y) = π y) (hxy : π x * π y = π y * π x) :
    x * y = y * x := by
  have hker : ∀ g : G, F (π g) = π g → g⁻¹ * Ft g ∈ π.ker := by
    intro g hg
    rw [MonoidHom.mem_ker, map_mul, map_inv, hF, hg, inv_mul_cancel]
  have hzx := hker x hx
  have hzy := hker y hy
  set zx : G := x⁻¹ * Ft x with hzxdef
  set zy : G := y⁻¹ * Ft y with hzydef
  have hFx : Ft x = x * zx := (mul_inv_cancel_left x (Ft x)).symm
  have hFy : Ft y = y * zy := (mul_inv_cancel_left y (Ft y)).symm
  have cx : ∀ a : G, a * zx = zx * a := Subgroup.mem_center_iff.mp (hπ hzx)
  have cy : ∀ a : G, a * zy = zy * a := Subgroup.mem_center_iff.mp (hπ hzy)
  have swap : ∀ (z a b : G), (∀ g, g * z = z * g) → a * z * b = a * b * z := by
    intro z a b hz
    rw [mul_assoc, ← hz b, ← mul_assoc]
  set c : G := x * y * x⁻¹ * y⁻¹ with hc
  have hcker : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hc]
    simp only [map_mul, map_inv]
    rw [hxy]
    group
  have hxy' : c * (y * x) = x * y := by rw [hc]; group
  have hF' : Ft c * (y * zy * (x * zx)) = x * zx * (y * zy) := by
    have := congrArg Ft hxy'
    simp only [map_mul, hFx, hFy] at this
    exact this
  have e1 : x * zx * (y * zy) = x * y * (zx * zy) := by
    rw [← mul_assoc, swap zx x y cx, mul_assoc]
  have e2 : y * zy * (x * zx) = y * x * (zx * zy) := by
    rw [← mul_assoc, swap zy y x cy, mul_assoc, cx zy]
  rw [e1, e2, ← mul_assoc] at hF'
  have h1 : Ft c = c := mul_right_cancel ((mul_right_cancel hF').trans hxy'.symm)
  have h2 : c = c⁻¹ := by rw [← hinv c hcker, h1]
  have e : c ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel c
  have h3 : c = 1 := by
    calc c = c ^ 2 * c := by rw [e, one_mul]
      _ = c ^ 3 := (pow_succ c 2).symm
      _ = 1 := hexp c hcker
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)

end CFSG.StandardType.LieCore.M6c
