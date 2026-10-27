module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowEp2Count

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.QuasithinUnique.Setup.X1

variable {W : Type} [CommGroup W] [Finite W] {p : ℕ} [Fact p.Prime] {a b : MulAut W}

theorem exists_index_eq_two_pow_mul_of_ep2 (hW : ∀ w : W, w * w = 1) (hp2 : p ≠ 2)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j)
    (h₀ : (fixV (Subgroup.zpowers b)).index = (fixV (Subgroup.zpowers a)).index)
    (h : ∀ i, 0 < i → i < p →
      (fixV (Subgroup.zpowers (a * b ^ i))).index = (fixV (Subgroup.zpowers a)).index) :
    ∃ j : ℕ, (fixV (Subgroup.zpowers a)).index = 2 ^ (p * orderOf (2 : ZMod p) * j) := by
  refine exists_index_eq_two_pow_mul_of_hyperplanes hW hp2 ha hb ha1 hab hba fun D hDA hD => ?_
  rcases eq_zpowers_of_le_sup_zpowers ha hb hab hDA hD with rfl | ⟨i, hi, rfl⟩
  · exact h₀
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [pow_zero, mul_one]
    · exact h i hi0 hi

omit [Finite W] in
theorem index_fixV_zpowers_ne_one (ha1 : a ≠ 1) : (fixV (Subgroup.zpowers a)).index ≠ 1 := by
  intro h
  apply ha1
  ext w
  have hw : w ∈ fixV (Subgroup.zpowers a) := by
    rw [Subgroup.index_eq_one.1 h]
    exact Subgroup.mem_top w
  exact mem_fixV_zpowers.1 hw

theorem two_pow_le_index_of_ep2 (hW : ∀ w : W, w * w = 1) (hp2 : p ≠ 2)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hab : a * b = b * a)
    (hba : ∀ j < p, b ≠ a ^ j)
    (h₀ : (fixV (Subgroup.zpowers b)).index = (fixV (Subgroup.zpowers a)).index)
    (h : ∀ i, 0 < i → i < p →
      (fixV (Subgroup.zpowers (a * b ^ i))).index = (fixV (Subgroup.zpowers a)).index) :
    2 ^ (p * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers a)).index := by
  obtain ⟨j, hj⟩ := exists_index_eq_two_pow_mul_of_ep2 hW hp2 ha hb ha1 hab hba h₀ h
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact index_fixV_zpowers_ne_one ha1 (by rw [hj, mul_zero, pow_zero])
  rw [hj]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj0))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
