module

public import CFSG.LocalAnalysis.SteinbergBNMiyamotoPrimaryLocalApplication
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL5

set_option linter.unusedSectionVars false

open Matrix CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]

@[expose] def un5tb_z : HypIndex 2 1 := .inr (.inl 0)

@[expose] def un5tb_emb : Fin 4 → HypIndex 2 1 :=
  ![.inl 0, .inl 1, .inr (.inr 1), .inr (.inr 0)]

theorem un5tb_sum (F : HypIndex 2 1 → K) :
    ∑ a, F a = F un5tb_z + ∑ k, F (un5tb_emb k) := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four, un5tb_z, un5tb_emb]
  ring

theorem un5tb_sq_sum [CharP K 2] (v : HypIndex 2 1 → K) :
    ∑ a, v (hypPartner a) * v a = v un5tb_z * v un5tb_z := by
  rw [un5tb_sum]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [Fin.sum_univ_four, un5tb_emb, un5tb_z, hypPartner]
  linear_combination (v (.inr (.inr 0)) * v (.inl 0) + v (.inr (.inr 1)) * v (.inl 1)) * h2

theorem un5tb_partner_z : hypPartner un5tb_z = un5tb_z := rfl

theorem un5tb_eq_partner_iff (b : HypIndex 2 1) : b = hypPartner b ↔ b = un5tb_z := by
  rcases b with i | k | i
  · simp [hypPartner, un5tb_z]
  · simp [hypPartner, un5tb_z, Subsingleton.elim k 0]
  · simp [hypPartner, un5tb_z]

theorem un5tb_row_z [CharP K 2] {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hJ : Mᵀ * hypGram 2 1 K * M = hypGram 2 1 K) (b : HypIndex 2 1) :
    M un5tb_z b = if b = un5tb_z then 1 else 0 := by
  have e := congrFun (congrFun hJ b) b
  rw [Matrix.mul_apply, hypGram_apply] at e
  simp only [mul_hypGram_apply, transpose_apply] at e
  rw [un5tb_sq_sum (fun a => M a b)] at e
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : (b = hypPartner b) ↔ b = un5tb_z := un5tb_eq_partner_iff b
  by_cases hbz : b = un5tb_z
  · rw [ite_eq_left hbz]
    rw [ite_eq_left (hb.mpr hbz)] at e
    have : (M un5tb_z b - 1) ^ 2 = 0 := by linear_combination e + (1 - M un5tb_z b) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  · rw [ite_eq_right hbz]
    rw [ite_eq_right (fun h' => hbz (hb.mp h'))] at e
    exact mul_self_eq_zero.mp e

theorem un5tb_mul_J_transpose {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hJ : Mᵀ * hypGram 2 1 K * M = hypGram 2 1 K) :
    M * hypGram 2 1 K * Mᵀ = hypGram 2 1 K := by
  have h1 : (hypGram 2 1 K * Mᵀ * hypGram 2 1 K) * M = 1 := by
    calc _ = hypGram 2 1 K * (Mᵀ * hypGram 2 1 K * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hypGram_mul_self]
  have h2 : M * (hypGram 2 1 K * Mᵀ * hypGram 2 1 K) = 1 := mul_eq_one_comm.mp h1
  calc M * hypGram 2 1 K * Mᵀ
      = M * hypGram 2 1 K * Mᵀ * (hypGram 2 1 K * hypGram 2 1 K) := by
        rw [hypGram_mul_self, Matrix.mul_one]
    _ = (M * (hypGram 2 1 K * Mᵀ * hypGram 2 1 K)) * hypGram 2 1 K := by
        simp only [Matrix.mul_assoc]
    _ = hypGram 2 1 K := by rw [h2, Matrix.one_mul]

theorem un5tb_col_z [CharP K 2] {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hJ : Mᵀ * hypGram 2 1 K * M = hypGram 2 1 K) (a : HypIndex 2 1) :
    M a un5tb_z = if a = un5tb_z then 1 else 0 := by
  have e := congrFun (congrFun (un5tb_mul_J_transpose hJ) a) a
  rw [Matrix.mul_apply, hypGram_apply] at e
  simp only [mul_hypGram_apply, transpose_apply] at e
  rw [un5tb_sq_sum (fun c => M a c)] at e
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : (a = hypPartner a) ↔ a = un5tb_z := un5tb_eq_partner_iff a
  by_cases haz : a = un5tb_z
  · rw [ite_eq_left haz]
    rw [ite_eq_left (hb.mpr haz)] at e
    have : (M a un5tb_z - 1) ^ 2 = 0 := by linear_combination e + (1 - M a un5tb_z) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  · rw [ite_eq_right haz]
    rw [ite_eq_right (fun h' => haz (hb.mp h'))] at e
    exact mul_self_eq_zero.mp e

theorem un5tb_emb_ne_z (i : Fin 4) : un5tb_emb i ≠ un5tb_z := by
  fin_cases i <;> simp [un5tb_emb, un5tb_z]

theorem un5tb_emb_injective : Function.Injective un5tb_emb := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [un5tb_emb]

theorem un5tb_cases (a : HypIndex 2 1) : a = un5tb_z ∨ ∃ k, a = un5tb_emb k := by
  rcases a with i | k | i
  · right
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · left
    simp [un5tb_z, Subsingleton.elim k 0]
  · right
    fin_cases i
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩

@[expose] def un5tb_blk (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) : Matrix (Fin 4) (Fin 4) K :=
  M.submatrix un5tb_emb un5tb_emb

theorem un5tb_blk_mul {M N : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hM : ∀ i, M (un5tb_emb i) un5tb_z = 0) :
    un5tb_blk (M * N) = un5tb_blk M * un5tb_blk N := by
  ext i j
  simp only [un5tb_blk, submatrix_apply, Matrix.mul_apply]
  rw [un5tb_sum, hM i, zero_mul, zero_add]

theorem un5tb_blk_J : un5tb_blk (hypGram 2 1 K) = miyamotoJ4 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [un5tb_blk, hypGram_apply, un5tb_emb, miyamotoJ4, hypPartner]

theorem un5tb_blk_transpose (M : Matrix (HypIndex 2 1) (HypIndex 2 1) K) :
    un5tb_blk Mᵀ = (un5tb_blk M)ᵀ := by
  ext i j
  rfl

theorem un5tb_blk_gram [CharP K 2] {M : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hJ : Mᵀ * hypGram 2 1 K * M = hypGram 2 1 K) :
    (un5tb_blk M)ᵀ * miyamotoJ4 K * un5tb_blk M = miyamotoJ4 K := by
  have hr : ∀ i, M un5tb_z (un5tb_emb i) = 0 := fun i => by
    rw [un5tb_row_z hJ, ite_eq_right (un5tb_emb_ne_z i)]
  have h1 : ∀ i, Mᵀ (un5tb_emb i) un5tb_z = 0 := fun i => by
    rw [transpose_apply, hr i]
  have h2 : ∀ i, (Mᵀ * hypGram 2 1 K) (un5tb_emb i) un5tb_z = 0 := fun i => by
    rw [mul_hypGram_apply, un5tb_partner_z, transpose_apply, hr i]
  calc (un5tb_blk M)ᵀ * miyamotoJ4 K * un5tb_blk M
      = un5tb_blk Mᵀ * un5tb_blk (hypGram 2 1 K) * un5tb_blk M := by
        rw [un5tb_blk_transpose, un5tb_blk_J]
    _ = un5tb_blk (Mᵀ * hypGram 2 1 K) * un5tb_blk M := by rw [un5tb_blk_mul h1]
    _ = un5tb_blk (Mᵀ * hypGram 2 1 K * M) := by rw [un5tb_blk_mul h2]
    _ = miyamotoJ4 K := by rw [hJ, un5tb_blk_J]

end CFSG.Quasithin.H13.F431.Un.OL5
