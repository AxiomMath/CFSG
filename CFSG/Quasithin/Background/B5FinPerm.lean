module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

namespace B5FinPerm

theorem allOnes_mul_self (n : ℕ) : G6.allOnes n * G6.allOnes n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, G6.allOnes, toAdd_ofAdd, toAdd_one, Pi.zero_apply]
  decide +revert

theorem mem_zpowers_allOnes_iff {n : ℕ} {x : G6.PermMod n} :
    x ∈ Subgroup.zpowers (G6.allOnes n) ↔ x = 1 ∨ x = G6.allOnes n := by
  have hg2 : G6.allOnes n * G6.allOnes n = 1 := allOnes_mul_self n
  constructor
  · rintro ⟨k, hk0⟩
    have hk : (G6.allOnes n) ^ k = (G6.allOnes n) ^ (k % 2) := by
      have h2 : (G6.allOnes n) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hg2
      calc (G6.allOnes n) ^ k = (G6.allOnes n) ^ (k % 2 + 2 * (k / 2)) := by
            rw [Int.emod_add_mul_ediv]
        _ = (G6.allOnes n) ^ (k % 2) * (G6.allOnes n) ^ (2 * (k / 2)) := zpow_add _ _ _
        _ = (G6.allOnes n) ^ (k % 2) * ((G6.allOnes n) ^ (2 : ℤ)) ^ (k / 2) := by
            congr 1
            exact zpow_mul _ _ _
        _ = (G6.allOnes n) ^ (k % 2) := by
            have h3 : (1 : G6.PermMod n) ^ (k / 2) = 1 := one_zpow _
            rw [h2, h3, mul_one]
    have hk1 : x = (G6.allOnes n) ^ (k % 2) := by rw [← hk]; exact hk0.symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk1, h0, zpow_zero]
    · right
      rw [hk1, h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

end B5FinPerm

end CFSG.Quasithin
