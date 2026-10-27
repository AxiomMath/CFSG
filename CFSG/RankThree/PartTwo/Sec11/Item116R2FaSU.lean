module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2Heis
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsThree

public section

open Subgroup CFSG.Assembly.LowTwoRank CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls

namespace CFSG.RankThree.PartTwo.Sec11

theorem heis_cubeDiag_mem {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) {ω : K} (hω3 : ω ^ 3 = 1)
    (hωq : ω ^ (q + 1) = 1) :
    glOfPowThree (cubeDiag ω) (cubeDiag_pow_three hω3) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ?_
  refine ⟨by simpa [coe_glOfPowThree] using det_cubeDiag hω3, ?_⟩
  simp only [coe_glOfPowThree, cubeDiag]
  rw [Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have h2 : (ω ^ 2) ^ q * ω ^ 2 = 1 := by
    calc (ω ^ 2) ^ q * ω ^ 2 = (ω ^ (q + 1)) ^ 2 := by ring
      _ = 1 := by rw [hωq, one_pow]
  have h1 : ω ^ q * ω = 1 := by rw [← pow_succ]; exact hωq
  fin_cases i <;> simp [h1, h2]

theorem heis_cycMat_mem {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) :
    glOfPowThree (cycMat (K := K)) (cycMat_pow_three (K := K)) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ?_
  refine ⟨by simpa [coe_glOfPowThree] using det_cycMat, ?_⟩
  simp only [coe_glOfPowThree]
  have hmap : (cycMat : Matrix (Fin 3) (Fin 3) K).map (· ^ q) = cycMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cycMat, zero_pow hq]
  rw [hmap, cycMat_transpose, ← pow_succ, cycMat_pow_three]

theorem heis_scalar_mem {K : Type} [Field K] {q : ℕ} (hq : q ≠ 0) {ω : K} (hω0 : ω ≠ 0)
    (hω3 : ω ^ 3 = 1) (hωq : ω ^ (q + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) ∈ StatedSU 3 q K := by
  refine Subgroup.subset_closure ?_
  refine ⟨?_, ?_⟩
  · simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0,
      Matrix.det_diagonal, Fin.prod_univ_three]
    linear_combination hω3
  · have h1 : ω ^ q * ω = 1 := by rw [← pow_succ]; exact hωq
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_mk0]
    rw [Matrix.diagonal_map (by simp [hq]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp [h1]

theorem heis_scalar_pow_three {K : Type} [Field K] {ω : K} (hω0 : ω ≠ 0) (hω3 : ω ^ 3 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) ^ 3 = (1 : GL (Fin 3) K) := by
  rw [← map_pow]
  have h : (Units.mk0 ω hω0) ^ 3 = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hω3, Units.val_one])
  rw [h, map_one]

theorem exists_heisenberg_statedSU {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) :
    ∃ H : Subgroup (StatedSU 3 q K), IsPGroup 3 H ∧
      ∃ x ∈ H, ∃ y ∈ H, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hq0 : q ≠ 0 := by omega
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq] <;> norm_num
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_three_dvd (K := K) (by rw [hK]; omega)
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  obtain ⟨m, hm⟩ : 3 ∣ q + 1 := by omega
  have hωq : ω ^ (q + 1) = 1 := by
    rw [hm, pow_mul, hω3, one_pow]
  obtain ⟨d, hd⟩ : ∃ d : StatedSU 3 q K,
      (d : GL (Fin 3) K) = glOfPowThree (cubeDiag ω) (cubeDiag_pow_three hω3) :=
    ⟨⟨_, heis_cubeDiag_mem hq0 hω3 hωq⟩, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : StatedSU 3 q K,
      (P : GL (Fin 3) K) = glOfPowThree (cycMat (K := K)) (cycMat_pow_three (K := K)) :=
    ⟨⟨_, heis_cycMat_mem hq0⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : StatedSU 3 q K,
      (z : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω hω0) :=
    ⟨⟨_, heis_scalar_mem hq0 hω0 hω3 hωq⟩, rfl⟩
  have hd3 : d ^ 3 = 1 := Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hd]
    exact glOfPowThree_pow_three _ _)
  have hP3 : P ^ 3 = 1 := Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hP]
    exact glOfPowThree_pow_three _ _)
  have hz3 : z ^ 3 = 1 := Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hz]
    exact heis_scalar_pow_three hω0 hω3)
  have hzd : z * d = d * z := Subtype.ext (by
    simp only [Subgroup.coe_mul, hz, hd]
    exact Matrix.GeneralLinearGroup.scalar_commute _ _)
  have hzP : z * P = P * z := Subtype.ext (by
    simp only [Subgroup.coe_mul, hz, hP]
    exact Matrix.GeneralLinearGroup.scalar_commute _ _)
  have hdP : d * P = P * d * z := Subtype.ext (by
    simp only [Subgroup.coe_mul, hd, hP, hz]
    refine Units.ext ?_
    simp only [Units.val_mul, coe_glOfPowThree, Matrix.GeneralLinearGroup.coe_scalar,
      Units.val_mk0]
    rw [cycMat_mul_cubeDiag hω3] <;> simp [Matrix.scalar_apply])
  have hnc : d * P ≠ P * d := by
    intro h
    have hz1 : z = 1 := mul_left_cancel (a := P * d) (by rw [mul_one, ← hdP]; exact h)
    have h00 : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
      rw [hz1]; simp
    rw [hz] at h00
    simp [Matrix.scalar_apply] at h00
    exact hω1 h00
  have hH : IsPGroup 3 (Subgroup.closure ({d, P, z} : Set (StatedSU 3 q K))) :=
    isPGroup_closure_heisenberg hd3 hP3 hz3 hzd hzP hdP
  exact ⟨Subgroup.closure ({d, P, z} : Set (StatedSU 3 q K)), hH, d,
    Subgroup.subset_closure (by simp), P, Subgroup.subset_closure (by simp), hd3, hP3, hnc⟩

end CFSG.RankThree.PartTwo.Sec11
