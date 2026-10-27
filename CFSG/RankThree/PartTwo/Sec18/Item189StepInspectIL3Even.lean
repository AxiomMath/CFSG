module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL3EvenTools

public section

namespace CFSG.RankThree.PartTwo.Sec18

theorem inspect189L3Even : Inspect189L3Even := by
  intro Y _ _ X Q x n hD hn ⟨e⟩
  exfalso
  obtain ⟨S, hS⟩ := hD.sylow.inf_of_le_normalizer (N := X) le_top
    (Subgroup.normalizer_eq_top_iff.2 hD.normal).ge
  have hmem : ∀ y : X, y ∈ (S : Subgroup X) ↔ (y : Y) ∈ Q := fun y => by
    have h1 := Subgroup.mem_map_iff_mem X.subtype_injective (K := (S : Subgroup X)) (x := y)
    rw [hS, Subgroup.mem_inf] at h1
    exact ⟨fun h => (h1.2 h).1, fun h => h1.1 ⟨h, y.2⟩⟩
  have hxS : (⟨x, hD.mem⟩ : X) ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    exact Subgroup.mem_normalizer_iff.1 hD.mem_normalizer y
  have hx : orderOf (⟨x, hD.mem⟩ : X) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hD.orderOf_eq
  have h1 := eq_one_of_mem_normalizer_projSL189 hn e S hxS
    (by rw [← hx]; exact pow_orderOf_eq_one _)
  rw [h1, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.RankThree.PartTwo.Sec18
