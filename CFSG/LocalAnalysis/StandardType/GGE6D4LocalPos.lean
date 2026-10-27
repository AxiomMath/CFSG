module

public import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

namespace E6D4Pos

variable {G : Type} [Group G]

theorem card_inf_centralizer [Finite G] {B E J : Subgroup G} (hE : IsElemAbelian 3 E)
    (hBE : B ≤ E) (hidx : Nat.card E ≤ 3 * Nat.card B)
    (hD : Nat.card (B ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2) :
    Nat.card (E ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 2 ∨
      Nat.card (E ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := E ⊓ Subgroup.centralizer (J : Set G) with hC
  have hBC : B ⊓ C = B ⊓ Subgroup.centralizer (J : Set G) := by
    rw [hC, ← inf_assoc, inf_eq_left.mpr hBE]
  have h1 := Subgroup.relIndex_mul_card B C
  have h2 := Subgroup.relIndex_mul_card B E
  rw [inf_eq_left.mpr hBE] at h2
  have hidx' : B.relIndex E ≤ 3 := by
    rw [← h2] at hidx
    exact Nat.le_of_mul_le_mul_right hidx Nat.card_pos
  have hne : B.relIndex E ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := E)).ne' h2.symm
  have hle : B.relIndex C ≤ B.relIndex E := Subgroup.relIndex_le_of_le_right inf_le_left hne
  rw [hBC, hD] at h1
  have hCp : IsPGroup 3 C := (hE.mono inf_le_left).isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hCp
  have hup : 3 ^ k ≤ 3 ^ 3 := by
    rw [← hk, ← h1]
    calc B.relIndex C * 3 ^ 2 ≤ 3 * 3 ^ 2 := Nat.mul_le_mul_right _ (hle.trans hidx')
      _ = 3 ^ 3 := by norm_num
  have hlo : 3 ^ 2 ≤ 3 ^ k := by
    rw [← hk, ← h1]
    have hpos : 0 < B.relIndex C := by
      rcases Nat.eq_zero_or_pos (B.relIndex C) with h0 | h0
      · rw [h0, zero_mul] at h1
        exact absurd h1.symm (Nat.card_pos (α := C)).ne'
      · exact h0
    exact Nat.le_mul_of_pos_left _ hpos
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hup
  have hk2 : 2 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hlo
  rw [hk]
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

end E6D4Pos

end CFSG.StandardType

end
