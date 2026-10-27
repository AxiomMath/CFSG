module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.TwE6D3

section Core

variable {G R : Type} [Group G] [Group R] {ψ : G →* R}

theorem exists_mul_of_map_eq (hker : ψ.ker ≤ Subgroup.center G) {x y : G} (h : ψ x = ψ y) :
    ∃ z ∈ Subgroup.center G, y = x * z :=
  ⟨x⁻¹ * y, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]),
    (mul_inv_cancel_left x y).symm⟩

theorem eq_one_of_eq_inv_of_pow_three {x : G} (h3 : x ^ 3 = 1) (h : x = x⁻¹) : x = 1 := by
  have h2 : x * x = 1 := by nth_rw 2 [h]; exact mul_inv_cancel x
  calc x = x ^ 3 * (x * x)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem comm_eq_of_map_eq (hker : ψ.ker ≤ Subgroup.center G) {x x' y y' : G}
    (hx : ψ x = ψ x') (hy : ψ y = ψ y') : x' * y' * x'⁻¹ * y'⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  obtain ⟨z, hz, rfl⟩ := exists_mul_of_map_eq hker hx
  obtain ⟨z', hz', rfl⟩ := exists_mul_of_map_eq hker hy
  have h1 := (Subgroup.mem_center_iff.mp hz (y * z')).symm
  have h2 := Subgroup.mem_center_iff.mp hz' x⁻¹
  calc x * z * (y * z') * (x * z)⁻¹ * (y * z')⁻¹
      = x * (z * (y * z')) * z⁻¹ * x⁻¹ * (y * z')⁻¹ := by group
    _ = x * (y * z' * z) * z⁻¹ * x⁻¹ * (y * z')⁻¹ := by rw [h1]
    _ = x * y * (z' * x⁻¹) * z'⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * z') * z'⁻¹ * y⁻¹ := by rw [← h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

variable (hker : ψ.ker ≤ Subgroup.center G) (h3 : ∀ z ∈ Subgroup.center G, z ^ 3 = 1)
include hker h3

theorem commute_of_refl {u v w : G} {k : ℕ} (hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center G)
    (hu : ψ (w * u * w⁻¹) = ψ (v ^ k * u)) (hv : ψ (w * v * w⁻¹) = ψ v⁻¹) : u * v = v * u := by
  have hcc := Subgroup.mem_center_iff.mp hc
  have hci := Subgroup.mem_center_iff.mp (inv_mem hc) (v ^ k * v⁻¹)
  have h1 : u * v * u⁻¹ * v⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by
    calc u * v * u⁻¹ * v⁻¹ = w * (u * v * u⁻¹ * v⁻¹) * w⁻¹ := by
          rw [hcc w, mul_inv_cancel_right]
      _ = w * u * w⁻¹ * (w * v * w⁻¹) * (w * u * w⁻¹)⁻¹ * (w * v * w⁻¹)⁻¹ := by group
      _ = v ^ k * u * v⁻¹ * (v ^ k * u)⁻¹ * v⁻¹⁻¹ := comm_eq_of_map_eq hker hu.symm hv.symm
      _ = v ^ k * v⁻¹ * (u * v * u⁻¹ * v⁻¹)⁻¹ * ((v ^ k)⁻¹ * v) := by group
      _ = (u * v * u⁻¹ * v⁻¹)⁻¹ * (v ^ k * v⁻¹) * ((v ^ k)⁻¹ * v) := by rw [hci]
      _ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  have h2 := eq_one_of_eq_inv_of_pow_three (h3 _ hc) h1
  calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
    _ = v * u := by rw [h2, one_mul]

theorem pow_three_of_refl {v w : G} (hv3 : v ^ 3 ∈ Subgroup.center G)
    (hv : ψ (w * v * w⁻¹) = ψ v⁻¹) : v ^ 3 = 1 := by
  obtain ⟨z, hz, hz'⟩ := exists_mul_of_map_eq hker hv.symm
  have h1 : w * v ^ 3 * w⁻¹ = v ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hv3 w, mul_inv_cancel_right]
  have h2 : w * v ^ 3 * w⁻¹ = (v ^ 3)⁻¹ := by
    rw [← conj_pow, hz', Commute.mul_pow (Subgroup.mem_center_iff.mp hz v⁻¹), h3 z hz, mul_one,
      inv_pow]
  exact eq_one_of_eq_inv_of_pow_three (h3 _ hv3) (h1.symm.trans h2)

theorem fix_of_refl {a : MulAut G} (haZ : ∀ z ∈ Subgroup.center G, a z = z) {v w : G} {k : ℕ}
    (hav : ψ (a v) = ψ v) (haw : ψ (a w) = ψ ((v ^ k)⁻¹ * w)) (hv : ψ (w * v * w⁻¹) = ψ v⁻¹) :
    a v = v := by
  obtain ⟨t, ht, hat⟩ := exists_mul_of_map_eq hker hav.symm
  obtain ⟨z, hz, haz⟩ := exists_mul_of_map_eq hker haw.symm
  have hc : w * v * w⁻¹ * v ∈ Subgroup.center G :=
    hker (by rw [MonoidHom.mem_ker, map_mul, hv, map_inv, inv_mul_cancel])
  have hcc := Subgroup.mem_center_iff.mp hc
  have htc := Subgroup.mem_center_iff.mp ht
  have hzc := Subgroup.mem_center_iff.mp hz
  have h1 : a (w * v * w⁻¹ * v) = w * v * w⁻¹ * v * (t * t) := by
    rw [map_mul, map_mul, map_mul, map_inv, hat, haz]
    calc (v ^ k)⁻¹ * w * z * (v * t) * ((v ^ k)⁻¹ * w * z)⁻¹ * (v * t)
        = (v ^ k)⁻¹ * w * (z * (v * t)) * z⁻¹ * w⁻¹ * v ^ k * (v * t) := by group
      _ = (v ^ k)⁻¹ * w * (v * t * z) * z⁻¹ * w⁻¹ * v ^ k * (v * t) := by rw [← hzc (v * t)]
      _ = (v ^ k)⁻¹ * w * v * (t * (w⁻¹ * v ^ k * v)) * t := by group
      _ = (v ^ k)⁻¹ * w * v * (w⁻¹ * v ^ k * v * t) * t := by rw [← htc (w⁻¹ * v ^ k * v)]
      _ = (v ^ k)⁻¹ * (w * v * w⁻¹ * v) * (v⁻¹ * v ^ k * v) * (t * t) := by group
      _ = w * v * w⁻¹ * v * (v ^ k)⁻¹ * (v⁻¹ * v ^ k * v) * (t * t) := by rw [hcc (v ^ k)⁻¹]
      _ = w * v * w⁻¹ * v * (t * t) := by group
  rw [haZ _ hc] at h1
  have htt : t * t = 1 := mul_left_cancel (h1.symm.trans (mul_one _).symm)
  rw [hat, eq_one_of_eq_inv_of_pow_three (h3 t ht) (eq_inv_of_mul_eq_one_left htt), mul_one]

end Core

end CFSG.StandardType.TwE6D3
