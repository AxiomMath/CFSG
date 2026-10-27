module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem mem_of_conj_mem_of_centralizer_le {G : Type} [Group G] {Y : Subgroup G} {b z g : G}
    (hC : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    (hz : ∃ y ∈ Y, z = y * b * y⁻¹) (hg : g * z * g⁻¹ ∈ Y) : g ∈ Y := by
  obtain ⟨y, hy, rfl⟩ := hz
  have h1 : (g * y) * b * (g * y)⁻¹ ∈ Y := by
    have h : (g * y) * b * (g * y)⁻¹ = g * (y * b * y⁻¹) * g⁻¹ := by group
    rw [h]
    exact hg
  obtain ⟨y₁, hy₁, h2⟩ := hfus (g * y) h1
  have h3 : y₁⁻¹ * (g * y) ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (y₁⁻¹ * (g * y)) = y₁⁻¹ * (y₁ * h * y₁⁻¹) * (g * y) := by group
      _ = y₁⁻¹ * ((g * y) * h * (g * y)⁻¹) * (g * y) := by rw [h2]
      _ = (y₁⁻¹ * (g * y)) * h := by group
  have h4 : y₁ * (y₁⁻¹ * (g * y)) * y⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem hy₁ (hC h3)) (Y.inv_mem hy)
  simpa using h4

end CFSG.StandardType.FrameRoute.FS81

end
