module

public import CFSG.Quasithin.Recognition.M12AscD7

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem pow3_D {d : G} (hd : d ∈ c.D) : d * d * d = 1 := by
  obtain ⟨a, ha, rfl⟩ := (mem_D c).1 hd
  rw [← map_mul, ← map_mul]
  have : ∀ a ∈ D6l, a * a * a = 1 := by decide +kernel
  rw [this a ha, map_one]

theorem b_inverts_D
    {d : G} (hd : d ∈ c.D) : (c.u' * z) * d * (c.u' * z)⁻¹ = d⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := (mem_D c).1 hd
  have key : pb * a * pb⁻¹ = a⁻¹ := by
    have : ∀ a ∈ D6l, pb * a * pb⁻¹ = a⁻¹ := by decide +kernel
    exact this a ha
  have e : c.ρ pb * c.ρ a * (c.ρ pb)⁻¹ = c.ρ (pb * a * pb⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [← c.ρ_pb, e, key, map_inv]

theorem b_comm_z : z * (c.u' * z) = (c.u' * z) * z := by
  have := c.u_facts.2.2
  calc z * (c.u' * z) = (z * c.u') * z := by group
    _ = (c.u' * z) * z := by rw [this]

theorem b_inv_eq : (c.u' * z)⁻¹ = c.u' * z := inv_eq_of_mul_eq_one_right c.b_sq

theorem eq_one_of_comm_b
    {d : G} (hd : d ∈ c.D) (h : (c.u' * z) * d = d * (c.u' * z)) : d = 1 := by
  have h1 := c.b_inverts_D hd
  have h2 : (c.u' * z) * d * (c.u' * z)⁻¹ = d := by
    calc (c.u' * z) * d * (c.u' * z)⁻¹ = (d * (c.u' * z)) * (c.u' * z)⁻¹ := by rw [h]
      _ = d := by group
  have h3 : d = d⁻¹ := by rw [← h1, h2]
  have hdd : d * d = 1 := by
    calc d * d = d * d⁻¹ := by rw [← h3]
      _ = 1 := by group
  calc d = d * d * d := by rw [hdd, one_mul]
    _ = 1 := c.pow3_D hd

theorem frattini_mem
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {y : G} (h : OuterData c y) {g : G} (hg : g ∈ Subgroup.normalizer (c.D : Set G)) :
    g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ ∈ c.D := by
  apply c.centralizer_D_le hyp h27 h
  rw [mem_C]
  intro d hd
  have hb := c.b_inv_eq
  have he : g⁻¹ * d * g ∈ c.D := (Subgroup.mem_normalizer_iff''.1 hg d).1 hd
  have he' : (g⁻¹ * d * g)⁻¹ ∈ c.D := inv_mem he
  have h1 : (c.u' * z)⁻¹ * d * (c.u' * z) = d⁻¹ := by
    rw [hb]
    have := c.b_inverts_D hd
    rw [hb] at this
    exact this
  have h2 := c.b_inverts_D he'
  rw [inv_inv] at h2
  have key : g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ * d *
      (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹)⁻¹ = d := by
    calc g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ * d * (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹)⁻¹
        = g * ((c.u' * z) * (g⁻¹ * ((c.u' * z)⁻¹ * d * (c.u' * z)) * g) * (c.u' * z)⁻¹) * g⁻¹ := by
          group
      _ = g * ((c.u' * z) * (g⁻¹ * d⁻¹ * g) * (c.u' * z)⁻¹) * g⁻¹ := by rw [h1]
      _ = g * (g⁻¹ * d * g) * g⁻¹ := by
          rw [show g⁻¹ * d⁻¹ * g = (g⁻¹ * d * g)⁻¹ by group, h2]
      _ = d := by group
  calc g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ * d
      = (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ * d *
        (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹)⁻¹) *
        (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹) := by group
    _ = d * (g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹) := by rw [key]

end AscCox

end CFSG.Quasithin
