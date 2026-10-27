module

public import CFSG.Quasithin.Recognition.M12AscL3

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

theorem exists_model_of_isConj (m : AscModel z) {w : G} (hw : IsConj z w) : Nonempty (AscModel w) := by
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hw
  subst hc0
  exact ⟨m.conj c0⟩

theorem asc03Hyp_of_isConj [Finite G] (hyp : Asc03Hyp G z) {w : G} (hw : IsConj z w) :
    Asc03Hyp G w := by
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hw
  subst hc0
  exact asc03Hyp_conj hyp c0

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem z_sq (c : AscCox m) : z * z = 1 := by
  rw [← c.ρ_z, ← map_mul, Equiv.swap_mul_self, map_one]

theorem rho_x6 : c.ρ x6 = m.ψ mX := by
  unfold x6
  rw [map_mul, c.ρ_u, c.ρ_ux, ← mul_assoc, c.u_facts.1, one_mul]

theorem rho_x16 : c.ρ x16 = c.x1 := by
  unfold x16
  rw [map_mul, c.ρ_x1z, c.ρ_z, mul_assoc, c.z_sq, mul_one]

@[expose] noncomputable def Dl : List G :=
  [1, m.ψ mX, m.ψ mX * m.ψ mX, c.x1, c.x1 * m.ψ mX, c.x1 * (m.ψ mX * m.ψ mX), c.x1 * c.x1,
    c.x1 * c.x1 * m.ψ mX, c.x1 * c.x1 * (m.ψ mX * m.ψ mX)]

theorem map_D6l : D6l.map c.ρ = c.Dl := by
  simp [D6l, Dl, map_mul, map_one, c.rho_x6, c.rho_x16]

theorem mem_D_iff {g : G} : g ∈ c.D ↔ g ∈ c.Dl := by
  rw [← c.map_D6l, mem_D, List.mem_map]
  rfl

theorem x_mem_D : m.ψ mX ∈ c.D := by
  rw [mem_D_iff]
  simp [Dl]

theorem x1_mem_D : c.x1 ∈ c.D := by
  rw [mem_D_iff]
  simp [Dl]

theorem D_comm
    {d d' : G} (hd : d ∈ c.D) (hd' : d' ∈ c.D) : d * d' = d' * d := by
  obtain ⟨a, ha, rfl⟩ := (mem_D c).1 hd
  obtain ⟨a', ha', rfl⟩ := (mem_D c).1 hd'
  rw [← map_mul, ← map_mul]
  congr 1
  have : ∀ a ∈ D6l, ∀ a' ∈ D6l, a * a' = a' * a := by decide +kernel
  exact this a ha a' ha'

theorem centralizes_D_iff {g : G} :
    (∀ d ∈ c.D, g * d = d * g) ↔ g * m.ψ mX = m.ψ mX * g ∧ g * c.x1 = c.x1 * g := by
  constructor
  · intro h
    exact ⟨h _ c.x_mem_D, h _ c.x1_mem_D⟩
  · rintro ⟨hx, hx1⟩ d hd
    have hx' : Commute g (m.ψ mX) := hx
    have hx1' : Commute g c.x1 := hx1
    rw [mem_D_iff] at hd
    simp only [Dl, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact hx
    · exact (hx'.mul_right hx')
    · exact hx1
    · exact (hx1'.mul_right hx')
    · exact (hx1'.mul_right (hx'.mul_right hx'))
    · exact (hx1'.mul_right hx1')
    · exact ((hx1'.mul_right hx1').mul_right hx')
    · exact ((hx1'.mul_right hx1').mul_right (hx'.mul_right hx'))

theorem x1_cube : c.x1 * c.x1 * c.x1 = 1 := by
  have := pow_orderOf_eq_one c.x1
  rwa [c.x1_ord, pow_succ, pow_two] at this

theorem b_sq : (c.u' * z) * (c.u' * z) = 1 := by
  obtain ⟨h1, -, h3⟩ := c.u_facts
  calc c.u' * z * (c.u' * z) = c.u' * (z * c.u') * z := by group
    _ = c.u' * (c.u' * z) * z := by rw [h3]
    _ = (c.u' * c.u') * (z * z) := by group
    _ = 1 := by rw [h1, c.z_sq, one_mul]

end AscCox

end CFSG.Quasithin
