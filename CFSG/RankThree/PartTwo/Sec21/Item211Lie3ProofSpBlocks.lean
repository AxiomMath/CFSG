module

public import CFSG.RankThree.SubgroupLists.SymplecticPlusBlock
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie3Proof

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.RankThree.SubgroupLists (plusBlock minusBlock tStdMat stdSign
  entry_eq_zero_of_commute_tStd one_ne_neg_one_of_two stdSign_inl_zero stdSign_inr_zero
  stdSign_inl_one stdSign_inr_one spGram transpose_mul_spGram_mul)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat)

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem plusBlock_add (M N : Matrix V₄ V₄ K) : plusBlock (M + N) = plusBlock M + plusBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_smul (c : K) (M : Matrix V₄ V₄ K) : plusBlock (c • M) = c • plusBlock M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_sub (M N : Matrix V₄ V₄ K) : plusBlock (M - N) = plusBlock M - plusBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem plusBlock_neg (M : Matrix V₄ V₄ K) : plusBlock (-M) = -plusBlock M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock]

theorem minusBlock_add (M N : Matrix V₄ V₄ K) :
    minusBlock (M + N) = minusBlock M + minusBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem minusBlock_smul (c : K) (M : Matrix V₄ V₄ K) : minusBlock (c • M) = c • minusBlock M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem minusBlock_sub (M N : Matrix V₄ V₄ K) :
    minusBlock (M - N) = minusBlock M - minusBlock N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem minusBlock_neg (M : Matrix V₄ V₄ K) : minusBlock (-M) = -minusBlock M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem minusBlock_one : minusBlock (1 : Matrix V₄ V₄ K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock]

theorem plusBlock_tStdMat : plusBlock (tStdMat : Matrix V₄ V₄ K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock, tStdMat, stdSign]

theorem minusBlock_tStdMat : minusBlock (tStdMat : Matrix V₄ V₄ K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minusBlock, tStdMat, stdSign]

theorem offBlock_eq_zero (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) :
    M (Sum.inl 0) (Sum.inl 1) = 0 ∧ M (Sum.inl 0) (Sum.inr 1) = 0 ∧
      M (Sum.inr 0) (Sum.inl 1) = 0 ∧ M (Sum.inr 0) (Sum.inr 1) = 0 ∧
      M (Sum.inl 1) (Sum.inl 0) = 0 ∧ M (Sum.inl 1) (Sum.inr 0) = 0 ∧
      M (Sum.inr 1) (Sum.inl 0) = 0 ∧ M (Sum.inr 1) (Sum.inr 0) = 0 := by
  have hne := one_ne_neg_one_of_two h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine entry_eq_zero_of_commute_tStd h2 hM ?_ <;>
    simp only [stdSign_inl_zero, stdSign_inr_zero, stdSign_inl_one, stdSign_inr_one] <;>
    first | exact hne | exact hne.symm

theorem minusBlock_mul (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) (N : Matrix V₄ V₄ K) :
    minusBlock (M * N) = minusBlock M * minusBlock N := by
  obtain ⟨-, -, -, -, z1, z2, z3, z4⟩ := offBlock_eq_zero h2 hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4]

theorem det_minusBlock (h2 : (2 : K) ≠ 0) {g : GL V₄ K} (hg : g ∈ StatedSp 2 K)
    (hgt : (g : Matrix V₄ V₄ K) * tStdMat = tStdMat * (g : Matrix V₄ V₄ K)) :
    (minusBlock (g : Matrix V₄ V₄ K)).det = 1 := by
  obtain ⟨z1, -, z3, -, -, -, -, -⟩ := offBlock_eq_zero h2 hgt
  have h := congrFun (congrFun (transpose_mul_spGram_mul hg) (Sum.inl 1)) (Sum.inr 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.fromBlocks, Matrix.one_apply,
    z1, z3] at h
  rw [minusBlock, Matrix.det_fin_two_of]
  linear_combination h

theorem eq_of_plusBlock_minusBlock (h2 : (2 : K) ≠ 0) {M N : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) (hN : N * tStdMat = tStdMat * N)
    (hp : plusBlock M = plusBlock N) (hm : minusBlock M = minusBlock N) : M = N := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := offBlock_eq_zero h2 hM
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := offBlock_eq_zero h2 hN
  have p00 := congrFun (congrFun hp 0) 0
  have p01 := congrFun (congrFun hp 0) 1
  have p10 := congrFun (congrFun hp 1) 0
  have p11 := congrFun (congrFun hp 1) 1
  have m00 := congrFun (congrFun hm 0) 0
  have m01 := congrFun (congrFun hm 0) 1
  have m10 := congrFun (congrFun hm 1) 0
  have m11 := congrFun (congrFun hm 1) 1
  simp only [plusBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at p00 p01 p10 p11
  simp only [minusBlock, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at m00 m01 m10 m11
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
  all_goals first
    | exact p00 | exact p01 | exact p10 | exact p11
    | exact m00 | exact m01 | exact m10 | exact m11
    | exact a1.trans b1.symm | exact a2.trans b2.symm | exact a3.trans b3.symm
    | exact a4.trans b4.symm | exact a5.trans b5.symm | exact a6.trans b6.symm
    | exact a7.trans b7.symm | exact a8.trans b8.symm

theorem plusBlock_pairMat_mul_pairMat (A B : Matrix (Fin 2) (Fin 2) K) :
    plusBlock (pairMat (Sum.inl 0 : V₄) (Sum.inr 0) A * pairMat (Sum.inl 1 : V₄) (Sum.inr 1) B) =
      A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusBlock, pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply]

theorem minusBlock_pairMat_mul_pairMat (A B : Matrix (Fin 2) (Fin 2) K) :
    minusBlock (pairMat (Sum.inl 0 : V₄) (Sum.inr 0) A * pairMat (Sum.inl 1 : V₄) (Sum.inr 1) B) =
      B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [minusBlock, pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply]

theorem pairMat_mul_pairMat_commute (A B : Matrix (Fin 2) (Fin 2) K) :
    pairMat (Sum.inl 0 : V₄) (Sum.inr 0) A * pairMat (Sum.inl 1 : V₄) (Sum.inr 1) B * tStdMat =
      tStdMat * (pairMat (Sum.inl 0 : V₄) (Sum.inr 0) A *
        pairMat (Sum.inl 1 : V₄) (Sum.inr 1) B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pairMat, tStdMat, stdSign, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply]

theorem eq_pairMat_mul_pairMat (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) :
    M = pairMat (Sum.inl 0 : V₄) (Sum.inr 0) (plusBlock M) *
      pairMat (Sum.inl 1 : V₄) (Sum.inr 1) (minusBlock M) :=
  eq_of_plusBlock_minusBlock h2 hM (pairMat_mul_pairMat_commute _ _)
    (plusBlock_pairMat_mul_pairMat _ _).symm (minusBlock_pairMat_mul_pairMat _ _).symm

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
