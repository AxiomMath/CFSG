module

public import CFSG.Timmesfeld.Bridge.Asc72Minimal

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G]

theorem conj_mem_conjOrbit {M : Subgroup G} {u k x : G} (hk : k ∈ M)
    (hx : x ∈ conjOrbit M u) : k * x * k⁻¹ ∈ conjOrbit M u := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨k * m, M.mul_mem hk hm, by group⟩

theorem disjoint_conjOrbit_of_not_mem {M : Subgroup G} {u x : G}
    (hx : x ∉ conjOrbit M u) : Disjoint (conjOrbit M u) (conjOrbit M x) := by
  rw [Set.disjoint_left]
  rintro y ⟨k, hk, hky⟩ ⟨k', hk', hky'⟩
  apply hx
  refine ⟨k'⁻¹ * k, M.mul_mem (M.inv_mem hk') hk, ?_⟩
  calc x = k'⁻¹ * y * k' := by rw [hky']; group
    _ = k'⁻¹ * (k * u * k⁻¹) * k' := by rw [hky]
    _ = (k'⁻¹ * k) * u * (k'⁻¹ * k)⁻¹ := by group

end CFSG.Timmesfeld.Bridge.Asc72
