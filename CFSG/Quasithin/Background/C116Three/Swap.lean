module

public import CFSG.Quasithin.Background.C116Two.Ctx

public section

namespace CFSG.Quasithin.C116Three

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem baum_le_normalizer_of_fixedVector {T V L : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hVT : V ≤ T)
    (hfv : ∃ u ∈ V, (∃ l ∈ L, l * u ≠ u * l) ∧ (∀ j ∈ thompsonJ T, j * u = u * j) ∧
      ∀ x ∈ T, x ∉ Subgroup.normalizer (L : Set G) →
        ∀ l ∈ L, (x * l * x⁻¹) * u = u * (x * l * x⁻¹)) :
    baum T ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨u, huV, ⟨l, hl, hlu⟩, hJu, hx⟩ := hfv
  intro x hxB
  by_contra hxN
  have huΩ := C116Two.mem_omegaOneCenter_of_centralizes hVe hVT huV hJu
  have hux : u * x = x * u := Subgroup.mem_centralizer_iff.mp hxB.2 u huΩ
  have hxinvN : x⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun hh =>
    hxN (by simpa using (Subgroup.inv_mem_iff _).mp hh)
  have hc := hx x⁻¹ (T.inv_mem hxB.1) hxinvN l hl
  rw [inv_inv] at hc
  have e1 : l = x * (x⁻¹ * l * x) * x⁻¹ := by group
  have e2 : u = x * u * x⁻¹ := by
    calc u = u * x * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [hux]
  apply hlu
  calc l * u = (x * (x⁻¹ * l * x) * x⁻¹) * (x * u * x⁻¹) := by rw [← e1, ← e2]
    _ = x * ((x⁻¹ * l * x) * u) * x⁻¹ := by group
    _ = x * (u * (x⁻¹ * l * x)) * x⁻¹ := by rw [hc]
    _ = (x * u * x⁻¹) * (x * (x⁻¹ * l * x) * x⁻¹) := by group
    _ = u * l := by rw [← e1, ← e2]

end CFSG.Quasithin.C116Three
