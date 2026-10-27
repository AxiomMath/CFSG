module

public import CFSG.RankThree.PartOne.KC.UnitaryCoordBlocks

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryCoord

variable {n : ℕ} {K : Type} [Field K]

theorem coordIncl_apply (i j : Fin n) (k : Fin n) (a : Fin 2) :
    coordIncl K i j k a = if k = ![i, j] a then 1 else 0 := rfl

theorem coordProj_apply (i j : Fin n) (a : Fin 2) (k : Fin n) :
    coordProj K i j a k = if k = ![i, j] a then 1 else 0 := rfl

theorem coordIncl_mul_coordProj_apply {i j : Fin n} (hij : i ≠ j) (k l : Fin n) :
    (coordIncl K i j * coordProj K i j) k l =
      if k = l ∧ (k = i ∨ k = j) then 1 else 0 := by
  simp only [Matrix.mul_apply, coordIncl_apply, coordProj_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hk : k = i
  · subst hk
    by_cases hl : l = k
    · subst hl; simp [hij]
    · simp [hl, Ne.symm hl, hij]
  · by_cases hkj : k = j
    · subst hkj
      by_cases hl : l = k
      · subst hl; simp [hij.symm]
      · simp [hl, Ne.symm hl, hij.symm]
    · simp [hk, hkj]

theorem coordEmbed_apply_of_not_mem_left {i j : Fin n} {k : Fin n} (hki : k ≠ i) (hkj : k ≠ j)
    (X : Matrix (Fin 2) (Fin 2) K) (l : Fin n) :
    coordEmbed K i j X k l = (1 : Matrix (Fin n) (Fin n) K) k l := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hki, hkj]

theorem coordEmbed_apply_of_not_mem_right {i j : Fin n} {l : Fin n} (hli : l ≠ i) (hlj : l ≠ j)
    (X : Matrix (Fin 2) (Fin 2) K) (k : Fin n) :
    coordEmbed K i j X k l = (1 : Matrix (Fin n) (Fin n) K) k l := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hli, hlj]

theorem coordEmbed_apply_ii {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X i i = X 0 0 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hij]

theorem coordEmbed_apply_ij {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X i j = X 0 1 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hij, hij.symm]

theorem coordEmbed_apply_ji {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X j i = X 1 0 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hij, hij.symm]

theorem coordEmbed_apply_jj {i j : Fin n} (hij : i ≠ j) (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X j j = X 1 1 := by
  simp [coordEmbed, coordIncl, coordProj, Matrix.mul_apply, Fin.sum_univ_two, hij.symm]

theorem coordProj_mul_coordIncl_of_disjoint {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) : coordProj K i j * coordIncl K k l = 0 := by
  ext a b
  simp only [Matrix.mul_apply, coordIncl_apply, coordProj_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  fin_cases a <;> fin_cases b <;> simp
  all_goals
    by_cases hm : m = i <;> by_cases hm' : m = j <;> by_cases hm'' : m = k <;>
      by_cases hm''' : m = l <;> simp_all

theorem coordEmbed_comm_of_disjoint {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (X Y : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K i j X * coordEmbed K k l Y = coordEmbed K k l Y * coordEmbed K i j X := by
  have h1 := coordProj_mul_coordIncl_of_disjoint (K := K) hik hil hjk hjl
  have h2 : coordProj K k l * coordIncl K i j = 0 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_zero] at this
    exact this
  unfold coordEmbed
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have e1 : coordIncl K i j * ((X - 1) * (coordProj K i j * (coordIncl K k l *
      ((Y - 1) * coordProj K k l)))) = 0 := by
    rw [← Matrix.mul_assoc (coordProj K i j), h1, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_zero]
  have e2 : coordIncl K k l * ((Y - 1) * (coordProj K k l * (coordIncl K i j *
      ((X - 1) * coordProj K i j)))) = 0 := by
    rw [← Matrix.mul_assoc (coordProj K k l), h2, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.mul_zero]
  rw [e1, e2]
  abel

theorem coordEmbed_eq_one_of_disjoint {i j k l : Fin n} (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) {X Y : Matrix (Fin 2) (Fin 2) K}
    (h : coordEmbed K i j X = coordEmbed K k l Y) : coordEmbed K i j X = 1 := by
  ext a b
  by_cases ha : a = i ∨ a = j
  · have hak : a ≠ k := by rcases ha with rfl | rfl <;> assumption
    have hal : a ≠ l := by rcases ha with rfl | rfl <;> assumption
    rw [h, coordEmbed_apply_of_not_mem_left hak hal]
  · push Not at ha
    rw [coordEmbed_apply_of_not_mem_left ha.1 ha.2]

theorem coordEmbed_conj {i j : Fin n} (hij : i ≠ j) {Y Y' : Matrix (Fin n) (Fin n) K}
    {Y₂ Y₂' : Matrix (Fin 2) (Fin 2) K} (hYY : Y * Y' = 1)
    (h1 : Y * coordIncl K i j = coordIncl K i j * Y₂)
    (h2 : Y' * coordIncl K i j = coordIncl K i j * Y₂')
    (h3 : coordProj K i j * Y' = Y₂' * coordProj K i j) (X : Matrix (Fin 2) (Fin 2) K) :
    Y₂ * Y₂' = 1 ∧ Y * coordEmbed K i j X * Y' = coordEmbed K i j (Y₂ * X * Y₂') := by
  have hπι := coordProj_mul_coordIncl (K := K) hij
  have h22 : Y₂ * Y₂' = 1 := by
    have h4 : coordIncl K i j * (Y₂ * Y₂') = coordIncl K i j := by
      calc coordIncl K i j * (Y₂ * Y₂') = (coordIncl K i j * Y₂) * Y₂' := by
            rw [Matrix.mul_assoc]
        _ = (Y * coordIncl K i j) * Y₂' := by rw [h1]
        _ = Y * (coordIncl K i j * Y₂') := by rw [Matrix.mul_assoc]
        _ = Y * (Y' * coordIncl K i j) := by rw [h2]
        _ = (Y * Y') * coordIncl K i j := by rw [Matrix.mul_assoc]
        _ = coordIncl K i j := by rw [hYY, Matrix.one_mul]
    have h5 := congrArg (fun M => coordProj K i j * M) h4
    simp only [← Matrix.mul_assoc, hπι, Matrix.one_mul] at h5
    exact h5
  refine ⟨h22, ?_⟩
  unfold coordEmbed
  have e1 : Y * (1 + coordIncl K i j * (X - 1) * coordProj K i j) * Y' =
      Y * Y' + (Y * coordIncl K i j) * (X - 1) * (coordProj K i j * Y') := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1, hYY, h1, h3]
  have e2 : coordIncl K i j * Y₂ * (X - 1) * (Y₂' * coordProj K i j) =
      coordIncl K i j * (Y₂ * X * Y₂' - 1) * coordProj K i j := by
    have : Y₂ * (X - 1) * Y₂' = Y₂ * X * Y₂' - 1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h22]
    calc coordIncl K i j * Y₂ * (X - 1) * (Y₂' * coordProj K i j)
        = coordIncl K i j * (Y₂ * (X - 1) * Y₂') * coordProj K i j := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [this]
  rw [e2]

end CFSG.RankThree.PartOne.KFU
