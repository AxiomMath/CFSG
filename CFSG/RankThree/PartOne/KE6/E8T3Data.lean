module

public import CFSG.RankThree.PartOne.KE.E8TwelveLattice
public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveMats
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.Assembly.LowTwoRankDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LieType.Steinberg.Adjoint Polynomial Matrix
open CFSG.RankThree.PartOne.KE (e8T12Word e8T12UList)

@[expose] def e8T3U : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd e8T12Word

@[expose] def e8T3W : WeylGroup Tag.E8 := e8T3U ^ 8

@[expose] def e8T6W : WeylGroup Tag.E8 := e8T3U ^ 20

@[expose] def e8T3MList : List (List ℤ) :=
  [[0, 0, 0, -1, 2, -1, 0, -1], [1, -1, -1, -1, 3, -1, 0, -1], [1, 0, -1, -2, 4, -1, -1, -1],
   [2, -1, -1, -3, 6, -2, -1, -1], [2, -1, -1, -2, 4, -1, -1, -1], [2, -1, -1, -1, 3, -1, -1, -1],
   [1, -1, 0, -1, 2, 0, -1, -1], [1, 0, 0, -1, 1, 0, 0, -1]]

@[expose] def e8T3Basis : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0, -1], [0, 1, 1, -1, 0, -1, 0, -1], [0, 1, 0, 0, 1, -1, 0, -2],
   [0, 2, 0, -1, 0, -1, 1, -3], [0, 2, 0, -1, 0, -1, 0, -2], [0, 2, 0, -1, 0, -1, 0, -1],
   [0, 1, 0, -1, 0, 0, 0, -1], [0, 1, 0, 0, 0, 0, 0, -1]]

@[expose] def e8T3BasisInv : List (List ℤ) :=
  [[1, 0, 0, 0, -1, 1, 0, 0], [0, 0, 0, 0, -1, 1, 0, 1], [0, 1, 0, 0, -1, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, -1, 1], [0, 0, 1, 0, -2, 1, 1, 0], [0, 0, 0, 0, -1, 0, 1, 1],
   [0, 0, 0, 1, -2, 1, 0, 0], [0, 0, 0, 0, -1, 1, 0, 0]]

@[expose] def e8T3Conj : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0],
   [0, 0, 1, -1, 0, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, -1, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, 1, -1]]

theorem weylMatrix_e8T3U : weylMatrix e8T3U = toMat Tag.E8.rank e8T12UList :=
  weylMatrix_wordProd_of (by decide +kernel)

theorem weylMatrix_e8T3W : weylMatrix e8T3W = toMat Tag.E8.rank e8T3MList := by
  rw [e8T3W, weylMatrix_pow, weylMatrix_e8T3U, ← toMat_lpow]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem weylMatrix_e8T6W : weylMatrix e8T6W = -toMat Tag.E8.rank e8T3MList := by
  rw [e8T6W, weylMatrix_pow, weylMatrix_e8T3U, ← toMat_lpow, ← toMat_lsmul_neg_one]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8T3_sq : toMat Tag.E8.rank e8T3MList * toMat Tag.E8.rank e8T3MList +
    toMat Tag.E8.rank e8T3MList + 1 = 0 := by
  rw [← toMat_lmul, ← toMat_ladd, ← toMat_lid, ← toMat_ladd, ← toMat_lzero]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8T3Basis_mul_inv : lmul Tag.E8.rank e8T3Basis e8T3BasisInv = lid Tag.E8.rank := by
  decide +kernel

theorem e8T3Conj_eq : e8T3Conj = lmul Tag.E8.rank (lmul Tag.E8.rank e8T3BasisInv e8T3MList)
    e8T3Basis := by
  decide +kernel

@[expose] def e8T3Conj6 : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 0], [1, -1, 0, 0, 0, 0], [0, 0, 0, -1, 0, 0], [0, 0, 1, -1, 0, 0],
    [0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1, -1]]

@[expose] def e8T3Conj4 : List (List ℤ) :=
  [[0, -1, 0, 0], [1, -1, 0, 0], [0, 0, 0, -1], [0, 0, 1, -1]]

theorem e8T3Conj_blocks :
    lowerLeftZero 2 6 e8T3Conj = true ∧ ltopLeft 2 e8T3Conj = [[0, -1], [1, -1]] ∧
      lbotRight 2 6 e8T3Conj = e8T3Conj6 := by
  decide +kernel

theorem e8T3Conj_blocks' :
    lowerLeftZero 2 4 e8T3Conj6 = true ∧ ltopLeft 2 e8T3Conj6 = [[0, -1], [1, -1]] ∧
      lbotRight 2 4 e8T3Conj6 = e8T3Conj4 := by
  decide +kernel

theorem e8T3Conj_blocks'' :
    lowerLeftZero 2 2 e8T3Conj4 = true ∧ ltopLeft 2 e8T3Conj4 = [[0, -1], [1, -1]] ∧
      lbotRight 2 2 e8T3Conj4 = [[0, -1], [1, -1]] := by
  decide +kernel

theorem charpoly_companion_two : (toMat 2 [[0, -1], [1, -1]]).charpoly = X ^ 2 + X + 1 := by
  have h : toMat 2 [[0, -1], [1, -1]] = !![0, -1; 1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.charpoly_fin_two]
  simp [Matrix.trace, Matrix.det_fin_two]

theorem charpoly_e8T3 : (toMat Tag.E8.rank e8T3MList).charpoly = (X ^ 2 + X + 1) ^ 4 := by
  have hc : (toMat Tag.E8.rank e8T3MList).charpoly = (toMat Tag.E8.rank e8T3Conj).charpoly := by
    rw [charpoly_eq_of_conj (B := toMat Tag.E8.rank e8T3Basis)
      (B' := toMat Tag.E8.rank e8T3BasisInv)
      (by rw [← toMat_lmul, e8T3Basis_mul_inv, toMat_lid]), e8T3Conj_eq, toMat_lmul, toMat_lmul]
  obtain ⟨h₁, h₂, h₃⟩ := e8T3Conj_blocks
  have hb₁ : (toMat 8 e8T3Conj).charpoly = (toMat 2 (ltopLeft 2 e8T3Conj)).charpoly *
      (toMat 6 (lbotRight 2 6 e8T3Conj)).charpoly := charpoly_eq_mul_of_blocks (k := 2) (m := 6) _ h₁
  obtain ⟨h₁', h₂', h₃'⟩ := e8T3Conj_blocks'
  have hb₂ : (toMat 6 e8T3Conj6).charpoly = (toMat 2 (ltopLeft 2 e8T3Conj6)).charpoly *
      (toMat 4 (lbotRight 2 4 e8T3Conj6)).charpoly := charpoly_eq_mul_of_blocks (k := 2) (m := 4) _ h₁'
  obtain ⟨h₁'', h₂'', h₃''⟩ := e8T3Conj_blocks''
  have hb₃ : (toMat 4 e8T3Conj4).charpoly = (toMat 2 (ltopLeft 2 e8T3Conj4)).charpoly *
      (toMat 2 (lbotRight 2 2 e8T3Conj4)).charpoly := charpoly_eq_mul_of_blocks (k := 2) (m := 2) _ h₁''
  rw [h₂'', h₃'', charpoly_companion_two] at hb₃
  rw [h₂', h₃', hb₃, charpoly_companion_two] at hb₂
  rw [h₂, h₃, hb₂, charpoly_companion_two] at hb₁
  rw [hc]
  refine Eq.trans hb₁ ?_
  ring

theorem det_sub_e8T3 (x : ℤ) :
    (Matrix.scalar (Fin Tag.E8.rank) x - toMat Tag.E8.rank e8T3MList).det =
      (x ^ 2 + x + 1) ^ 4 := by
  have h := congrArg (Polynomial.eval x) charpoly_e8T3
  rw [Matrix.eval_charpoly] at h
  simpa using h

@[expose] def e8T3We (ε : ℤ) : WeylGroup Tag.E8 := if ε = 1 then e8T3W else e8T6W

theorem e8T3We_one : e8T3We 1 = e8T3W := by simp [e8T3We]

theorem e8T3We_neg_one : e8T3We (-1) = e8T6W := by simp [e8T3We]

theorem weylMatrix_e8T3We {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    weylMatrix (e8T3We ε) = ε • toMat Tag.E8.rank e8T3MList := by
  rcases hε with rfl | rfl
  · rw [e8T3We_one, weylMatrix_e8T3W, one_smul]
  · rw [e8T3We_neg_one, weylMatrix_e8T6W, neg_one_smul]

theorem e8T3We_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (x : Fin Tag.E8.rank → ℤ) :
    e8T3We ε • x = ε • (e8T3W • x) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_e8T3We hε, weylMatrix_e8T3W,
    Matrix.smul_mulVec]

end CFSG.RankThree.PartOne.KE6
