module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem exists_alt8_config : ∃ x y g h : alternatingGroup (Fin 8), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧
    x * y = y * x ∧ g * x * g⁻¹ = x⁻¹ ∧ g * y * g⁻¹ = y ∧ h * x * h⁻¹ = x ∧ h * y * h⁻¹ = y⁻¹ ∧
    ∀ i j k l : Fin 3, x ^ (i : ℕ) * y ^ (j : ℕ) = x ^ (k : ℕ) * y ^ (l : ℕ) → i = k ∧ j = l := by
  refine ⟨⟨Equiv.swap (0 : Fin 8) 2 * Equiv.swap 0 1,
      Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ⟨Equiv.swap (3 : Fin 8) 5 * Equiv.swap 3 4,
      Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ⟨Equiv.swap (0 : Fin 8) 1 * Equiv.swap 6 7,
      Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩,
    ⟨Equiv.swap (3 : Fin 8) 4 * Equiv.swap 6 7,
      Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)⟩, ?_⟩
  decide +kernel

end CFSG.RankThree.PartTwo.KFacts
