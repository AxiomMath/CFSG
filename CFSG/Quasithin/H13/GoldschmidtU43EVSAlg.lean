module

public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.U43

variable {K : Type*} [Group K]

theorem u_comm_conj {a b u Z : K} (hZc : ∀ x : K, Z * x = x * Z) (hZ : Z * Z = 1)
    (ha : a * a = Z) (hb : b * b = Z) (hab : a * b = b * a) (hu : u * u = 1)
    (hub : u * b * u = a) : u * (b⁻¹ * u * b) = (b⁻¹ * u * b) * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have ha' : a⁻¹ = a * Z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ha, hZ])
  have hb' : b⁻¹ = b * Z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hb, hZ])
  have h1 : u * b⁻¹ * u = a⁻¹ := by
    calc u * b⁻¹ * u = u⁻¹ * b⁻¹ * u⁻¹ := by rw [hui]
      _ = (u * b * u)⁻¹ := by group
      _ = a⁻¹ := by rw [hub]
  have e1 : u * (b⁻¹ * u * b) = a⁻¹ * b := by
    calc u * (b⁻¹ * u * b) = (u * b⁻¹ * u) * b := by group
      _ = a⁻¹ * b := by rw [h1]
  have e2 : (b⁻¹ * u * b) * u = b⁻¹ * a := by
    calc (b⁻¹ * u * b) * u = b⁻¹ * (u * b * u) := by group
      _ = b⁻¹ * a := by rw [hub]
  rw [e1, e2, ha', hb']
  calc a * Z * b = a * (Z * b) := mul_assoc _ _ _
    _ = a * (b * Z) := by rw [hZc b]
    _ = (a * b) * Z := (mul_assoc _ _ _).symm
    _ = (b * a) * Z := by rw [hab]
    _ = b * (a * Z) := mul_assoc _ _ _
    _ = b * (Z * a) := by rw [hZc a]
    _ = b * Z * a := (mul_assoc _ _ _).symm

theorem uv_comm_conj {a b u v Z : K} (hZc : ∀ x : K, Z * x = x * Z) (hZ : Z * Z = 1)
    (ha : a * a = Z) (hb : b * b = Z) (hab : a * b = b * a) (hu : u * u = 1)
    (hub : u * b * u = a) (huv : u * v * u = v⁻¹) (hvb : v * b * v⁻¹ = b⁻¹) :
    (b⁻¹ * (u * v * Z) * b) * (u * v) = (u * v) * (b⁻¹ * (u * v * Z) * b) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hw2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = (u * v * u) * v := by group
      _ = v⁻¹ * v := by rw [huv]
      _ = 1 := inv_mul_cancel v
  have hwi : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right hw2
  have h1 : u * b⁻¹ * u = a⁻¹ := by
    calc u * b⁻¹ * u = u⁻¹ * b⁻¹ * u⁻¹ := by rw [hui]
      _ = (u * b * u)⁻¹ := by group
      _ = a⁻¹ := by rw [hub]
  have hvb' : v * b⁻¹ * v⁻¹ = b := by
    calc v * b⁻¹ * v⁻¹ = (v * b * v⁻¹)⁻¹ := by group
      _ = b := by rw [hvb, inv_inv]
  have hwb : (u * v) * b * (u * v) = a⁻¹ := by
    calc (u * v) * b * (u * v) = (u * v) * b * (u * v)⁻¹ := by rw [hwi]
      _ = u * (v * b * v⁻¹) * u⁻¹ := by group
      _ = a⁻¹ := by rw [hvb, hui, h1]
  have hwb' : (u * v) * b⁻¹ * (u * v) = a := by
    calc (u * v) * b⁻¹ * (u * v) = (u * v) * b⁻¹ * (u * v)⁻¹ := by rw [hwi]
      _ = u * (v * b⁻¹ * v⁻¹) * u⁻¹ := by group
      _ = a := by rw [hvb', hui, hub]
  have hab2 : (a * b) * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, hZ]
  have hinv : b⁻¹ * a⁻¹ = a * b := by
    rw [← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right hab2
  have core : (b⁻¹ * (u * v) * b) * (u * v) = (u * v) * (b⁻¹ * (u * v) * b) := by
    calc (b⁻¹ * (u * v) * b) * (u * v) = b⁻¹ * ((u * v) * b * (u * v)) := by group
      _ = b⁻¹ * a⁻¹ := by rw [hwb]
      _ = a * b := hinv
      _ = ((u * v) * b⁻¹ * (u * v)) * b := by rw [hwb']
      _ = (u * v) * (b⁻¹ * (u * v) * b) := by group
  have hc : b⁻¹ * (u * v * Z) * b = (b⁻¹ * (u * v) * b) * Z := by
    calc b⁻¹ * (u * v * Z) * b = b⁻¹ * (u * v) * (Z * b) := by group
      _ = b⁻¹ * (u * v) * (b * Z) := by rw [hZc b]
      _ = (b⁻¹ * (u * v) * b) * Z := by group
  rw [hc]
  calc (b⁻¹ * (u * v) * b * Z) * (u * v)
      = (b⁻¹ * (u * v) * b) * (Z * (u * v)) := by group
    _ = (b⁻¹ * (u * v) * b) * ((u * v) * Z) := by rw [hZc (u * v)]
    _ = ((b⁻¹ * (u * v) * b) * (u * v)) * Z := by group
    _ = ((u * v) * (b⁻¹ * (u * v) * b)) * Z := by rw [core]
    _ = (u * v) * (b⁻¹ * (u * v) * b * Z) := by group

end CFSG.Quasithin.H13.U43
