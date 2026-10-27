module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

theorem a6_exists_four_group : ∀ g : alternatingGroup (Fin 6), g ^ 3 = 1 → g ≠ 1 →
    ∃ v : alternatingGroup (Fin 6), v ^ 2 = 1 ∧ g * v * g⁻¹ ≠ v ∧
      (g * v * g⁻¹) * v = v * (g * v * g⁻¹) ∧ g * (g * v * g⁻¹) * g⁻¹ = v * (g * v * g⁻¹) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
