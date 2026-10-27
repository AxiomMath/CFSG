module

public import CFSG.Quasithin.Recognition.CertTwoLocalIndexTwo

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {N : Type*} [Group N]

theorem inf_eq (L : TwoLocalLattice N) : L.P₁ ⊓ L.P₂ = L.S := by
  rcases L.lattice (L.P₁ ⊓ L.P₂) (le_inf L.S_le_P₁ L.S_le_P₂) with h | h | h | h
  · exact h
  · exact absurd (by rw [← h]; exact inf_le_right) L.P₁_not_le_P₂
  · exact absurd (by rw [← h]; exact inf_le_left) L.P₂_not_le_P₁
  · exfalso
    have h1 : (⊤ : Subgroup N) ≤ L.P₁ := by rw [← h]; exact inf_le_left
    exact L.not_isTwoLocal_top (top_le_iff.1 h1 ▸ L.isTwoLocal_P₁)

theorem sup_eq_top (L : TwoLocalLattice N) : L.P₁ ⊔ L.P₂ = ⊤ := by
  rcases L.lattice (L.P₁ ⊔ L.P₂) (L.S_le_P₁.trans le_sup_left) with h | h | h | h
  · exact absurd (le_antisymm L.S_le_P₁ (by rw [← h]; exact le_sup_left)) L.S_ne_P₁
  · exact absurd (by rw [← h]; exact le_sup_right) L.P₂_not_le_P₁
  · exact absurd (by rw [← h]; exact le_sup_left) L.P₁_not_le_P₂
  · exact h

theorem isPGroup_inf (L : TwoLocalLattice N) : IsPGroup 2 ↥(L.P₁ ⊓ L.P₂) := by
  rw [inf_eq L]
  exact L.sylow.1

theorem faithful (L : TwoLocalLattice N) :
    (GoldAmalgam.ofSubgroupPair L.P₁ L.P₂).IsFaithful := by
  rw [GoldAmalgam.ofSubgroupPair_isFaithful_iff _ _ (sup_eq_top L)]
  intro Q hQ hle
  rw [inf_eq L] at hle
  exact L.O₂ Q hQ (L.sylow.1.to_le hle)

theorem index_left (L : TwoLocalLattice N) {a : ℕ} (hS : Nat.card L.S = 2 ^ a)
    (h₁ : Nat.card L.P₁ = 5 * 2 ^ a) :
    (GoldAmalgam.ofSubgroupPair L.P₁ L.P₂).edgeA.index = 5 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeA_index, inf_eq L]
  have h := Subgroup.relIndex_mul_card (H := L.S) (K := L.P₁)
  rw [inf_eq_left.2 L.S_le_P₁, hS, h₁] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem index_right (L : TwoLocalLattice N) {a : ℕ} (hS : Nat.card L.S = 2 ^ a)
    (h₂ : Nat.card L.P₂ = 3 * 2 ^ a) :
    (GoldAmalgam.ofSubgroupPair L.P₁ L.P₂).edgeB.index = 3 := by
  rw [GoldAmalgam.ofSubgroupPair_edgeB_index, inf_eq L]
  have h := Subgroup.relIndex_mul_card (H := L.S) (K := L.P₂)
  rw [inf_eq_left.2 L.S_le_P₂, hS, h₂] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

end CFSG.Quasithin.Fan86.Model
