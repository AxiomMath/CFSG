module

public import CFSG.Quasithin.Background.Ordering

public section

open scoped Pointwise

namespace CFSG.Quasithin

theorem conjClosure_sup_eq_of_le_normalizer {G : Type*} [Group G] {Z K T : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hTZ : T ≤ Subgroup.centralizer (Z : Set G)) :
    conjClosure Z (K ⊔ T) = conjClosure Z K := by
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    have hmem : h ∈ (K : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T hTK]
      exact hh
    obtain ⟨k, hk, t, ht, rfl⟩ := hmem
    have htz : t * z * t⁻¹ = z := by
      have hc := Subgroup.mem_centralizer_iff.mp (hTZ ht) z hz
      rw [hc.symm]
      group
    have e : k * t * z * (k * t)⁻¹ = k * (t * z * t⁻¹) * k⁻¹ := by group
    rw [e, htz]
    exact mem_conjClosure hk hz
  · exact conjClosure_mono le_rfl le_sup_left

end CFSG.Quasithin
