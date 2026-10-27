module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.Quasithin.S153N

theorem index_ne_three_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : 6 < Nat.card G) (H : Subgroup G) : H.index ≠ 3 := by
  intro h3
  have : H.FiniteIndex := ⟨by omega⟩
  have hdvd : H.normalCore.index ∣ H.index.factorial := H.index_normalCore_dvd_factorial_index
  have h6 : Nat.factorial 3 = 6 := rfl
  rw [h3, h6] at hdvd
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
  · rw [h, Subgroup.index_bot] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hH : H = ⊤ := top_le_iff.1 (h ▸ H.normalCore_le)
    rw [hH, Subgroup.index_top] at h3
    omega

end CFSG.Quasithin.S153N
