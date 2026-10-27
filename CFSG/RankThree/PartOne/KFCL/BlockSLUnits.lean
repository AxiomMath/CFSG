module

public import CFSG.RankThree.PartOne.KFCL.BlockSL

public section

namespace CFSG.RankThree.PartOne.KFCL.BlockSL

open Matrix

@[expose] noncomputable def ext1GL {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → Prop} [DecidablePred p] (A : GL {i // p i} K) : GL ι K :=
  ⟨ext1 p (A : Matrix {i // p i} {i // p i} K),
    ext1 p ((A⁻¹ : GL {i // p i} K) : Matrix {i // p i} {i // p i} K),
    by rw [← ext1_mul, Units.mul_inv, ext1_one],
    by rw [← ext1_mul, Units.inv_mul, ext1_one]⟩

theorem ext1GL_val {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → Prop} [DecidablePred p] (A : GL {i // p i} K) :
    (ext1GL A : Matrix ι ι K) = ext1 p (A : Matrix {i // p i} {i // p i} K) := rfl

theorem commute_diagonal_ext1 {K : Type*} [Field K] [DecidableEq K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : ι → K) (c : K) (A : Matrix {i // d i = c} {i // d i = c} K) :
    ext1 (fun i => d i = c) A * Matrix.diagonal d =
      Matrix.diagonal d * ext1 (fun i => d i = c) A := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : d i = d j
  · rw [hij, mul_comm]
  · have hne : i ≠ j := fun h => hij (by rw [h])
    by_cases hi : d i = c <;> by_cases hj : d j = c
    · exact absurd (hi.trans hj.symm) hij
    · simp [ext1_apply, hi, hj, hne]
    · simp [ext1_apply, hi, hj, hne]
    · simp [ext1_apply, hi, hj, hne]

theorem unitary_ext1 {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (A : Matrix {i // p i} {i // p i} K)
    {f : K → K} (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hA : (A.map f)ᵀ * A = 1) :
    ((ext1 p A).map f)ᵀ * ext1 p A = 1 := by
  set e := Equiv.sumCompl p with he
  have hM : ext1 p A = Matrix.reindex e e (Matrix.fromBlocks A 0 0 1) := rfl
  rw [hM]
  have hmap : (Matrix.reindex e e (Matrix.fromBlocks A 0 0 1)).map f =
      Matrix.reindex e e ((Matrix.fromBlocks A 0 0 1).map f) := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]
  rw [hmap, Matrix.transpose_reindex]
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [Matrix.map_zero f hf0, Matrix.map_one f hf0 hf1, Matrix.transpose_zero,
    Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, one_mul, mul_one,
    hA, Matrix.fromBlocks_one]
  rw [Matrix.submatrix_one_equiv]

end CFSG.RankThree.PartOne.KFCL.BlockSL

end
