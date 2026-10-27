module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.FixedPointFreeOutsideCentral
public import CFSG.Fischer.Classification.Basic.Heisenberg
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoHeisenberg

public section

namespace CFSG.StandardType.USixTwo.Extraspecial

open CFSG.Assembly Matrix
open CFSG.Fischer.Classification
open scoped commutatorElement

variable {K : Type} [Field K]

def A3 (ω : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![1, ω, ω ^ 2]

def P3 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

def F3 (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

def A6 (ω : K) : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, ω, ω ^ 2, 1, 1, 1]

def P6 : Matrix (Fin 6) (Fin 6) K :=
  !![0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

def P6i : Matrix (Fin 6) (Fin 6) K :=
  !![0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

def F6 (ω : K) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 1, 1, 0, 0, 0;
     1, ω, ω ^ 2, 0, 0, 0;
     1, ω ^ 2, ω, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

def D6 (ω : K) : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, ω, 1, ω ^ 2, 1, 1]

def blockDiag3 (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < 3 then
      if hj : (j : ℕ) < 3 then M ⟨i.val, hi⟩ ⟨j.val, hj⟩
      else if i = j then 1 else 0
    else if i = j then 1 else 0

@[simp] theorem finSumFinEquiv_symm_zero :
    (finSumFinEquiv (m := 3) (n := 3)).symm (0 : Fin 6) = Sum.inl 0 := rfl
@[simp] theorem finSumFinEquiv_symm_one :
    (finSumFinEquiv (m := 3) (n := 3)).symm (1 : Fin 6) = Sum.inl 1 := rfl
@[simp] theorem finSumFinEquiv_symm_two :
    (finSumFinEquiv (m := 3) (n := 3)).symm (2 : Fin 6) = Sum.inl 2 := rfl
@[simp] theorem finSumFinEquiv_symm_three :
    (finSumFinEquiv (m := 3) (n := 3)).symm (3 : Fin 6) = Sum.inr 0 := rfl
@[simp] theorem finSumFinEquiv_symm_four :
    (finSumFinEquiv (m := 3) (n := 3)).symm (4 : Fin 6) = Sum.inr 1 := rfl
@[simp] theorem finSumFinEquiv_symm_five :
    (finSumFinEquiv (m := 3) (n := 3)).symm (5 : Fin 6) = Sum.inr 2 := rfl

theorem blockDiag3_eq_reindex (M : Matrix (Fin 3) (Fin 3) K) :
    blockDiag3 M = Matrix.reindex (finSumFinEquiv (m := 3) (n := 3))
      (finSumFinEquiv (m := 3) (n := 3)) (Matrix.fromBlocks M 0 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag3, Matrix.reindex_apply, Matrix.fromBlocks]

theorem blockDiag3_det (M : Matrix (Fin 3) (Fin 3) K) :
    (blockDiag3 M).det = M.det := by
  rw [blockDiag3_eq_reindex, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one]

theorem det_F3 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (F3 ω).det = 1 := by
  simp [F3, Matrix.det_fin_three]
  grind

theorem F6_eq_blockDiag3_F3 (ω : K) : F6 ω = blockDiag3 (F3 ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F6, F3, blockDiag3]

theorem det_F6 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (F6 ω).det = 1 := by
  rw [F6_eq_blockDiag3_F3, blockDiag3_det, det_F3 hω h2]

theorem A6_eq_blockDiag3_A3 (ω : K) : A6 ω = blockDiag3 (A3 ω) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, A3, blockDiag3]

theorem P6_eq_blockDiag3_P3 : P6 = blockDiag3 (P3 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, P3, blockDiag3]

theorem det_A3 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (A3 ω).det = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  simp [A3, Matrix.det_diagonal, Fin.prod_univ_three]
  grind

theorem det_P3 : (P3 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [P3, Matrix.det_fin_three]

theorem A6_det {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (A6 ω).det = 1 := by
  rw [A6_eq_blockDiag3_A3, blockDiag3_det, det_A3 hω]

theorem P6_det : (P6 : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [P6_eq_blockDiag3_P3, blockDiag3_det, det_P3]

theorem D6_det {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (D6 ω).det = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  simp [D6, Matrix.det_diagonal, Fin.prod_univ_six]
  grind

theorem A6_unitary {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ((A6 ω).map (· ^ 2))ᵀ * A6 ω = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind

theorem P6_unitary :
    ((P6 : Matrix (Fin 6) (Fin 6) K).map (· ^ 2))ᵀ * P6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply]

theorem F6_unitary {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ((F6 ω).map (· ^ 2))ᵀ * F6 ω = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [F6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind

theorem D6_unitary {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ((D6 ω).map (· ^ 2))ᵀ * D6 ω = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [D6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind

def A6i (ω : K) : Matrix (Fin 6) (Fin 6) K := Matrix.diagonal ![1, ω ^ 2, ω, 1, 1, 1]

theorem A6_mul_A6i {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : A6 ω * A6i ω = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, A6i, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind

theorem A6i_mul_A6 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : A6i ω * A6 ω = 1 := by
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, A6i, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind

noncomputable def glA {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A6 ω) (by rw [A6_det hω]; exact one_ne_zero)

noncomputable def glP : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero P6 (by rw [P6_det]; exact one_ne_zero)

noncomputable def glF {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (F6 ω) (by rw [det_F6 hω h2]; exact one_ne_zero)

noncomputable def glD {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 6) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (D6 ω) (by rw [D6_det hω]; exact one_ne_zero)

theorem P6_mul_P6i : P6 * P6i = (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, P6i, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply]

theorem P6i_mul_P6 : P6i * P6 = (1 : Matrix (Fin 6) (Fin 6) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P6, P6i, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply]

noncomputable def glPi : GL (Fin 6) K :=
  ⟨P6i, P6, P6i_mul_P6, P6_mul_P6i⟩

noncomputable def glAi {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 6) K :=
  ⟨A6i ω, A6 ω, A6i_mul_A6 hω, A6_mul_A6i hω⟩

theorem glA_inv {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (glA hω)⁻¹ = glAi hω := by
  symm
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  change A6 ω * A6i ω = (1 : Matrix (Fin 6) (Fin 6) K)
  exact A6_mul_A6i hω

theorem glP_cube : glP ^ 3 = (1 : GL (Fin 6) K) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glP, P6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, pow_succ]

theorem glP_inv : (glP : GL (Fin 6) K)⁻¹ = glPi := by
  symm
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  change P6 * P6i = (1 : Matrix (Fin 6) (Fin 6) K)
  exact P6_mul_P6i

theorem glA_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (glA hω) ^ 3 = (1 : GL (Fin 6) K) := by
  apply Units.ext
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glA, A6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, pow_succ] <;> grind

theorem AP_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (glA hω * glP) ^ 3 = (1 : GL (Fin 6) K) := by
  apply Units.ext
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glA, glP, A6, P6, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.one_apply, pow_succ] <;> grind

theorem APinv_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (glA hω * glPi) ^ 3 = (1 : GL (Fin 6) K) := by
  apply Units.ext
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glA, glPi, A6, P6i, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.one_apply, pow_succ] <;> grind

noncomputable def B {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 6) K :=
  ⁅glA hω, glP⁆

theorem omega_ne_one {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) : ω ≠ 1 := by
  intro h1
  rw [h1] at hω
  have h3 : (3 : K) = 0 := by linear_combination hω
  have h3' : (3 : K) = 1 := by
    rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
  rw [h3'] at h3
  exact one_ne_zero h3

theorem B_eq_diag {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (h2 : (2 : K) = 0) :
    (B hω : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal ![ω, ω, ω, 1, 1, 1] := by
  unfold B
  rw [commutatorElement_def, glA_inv, glP_inv]
  change A6 ω * P6 * A6i ω * P6i = Matrix.diagonal ![ω, ω, ω, 1, 1, 1]
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, A6i, P6, P6i, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal] <;> grind

theorem F_mul_P {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * glP = glA hω * glF hω h2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glF, glP, glA, F6, P6, A6, Matrix.mul_apply, Fin.sum_univ_six] <;> grind

theorem F_mul_A {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * glA hω = glP ^ 2 * glF hω h2 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glF, glP, glA, F6, P6, A6, Matrix.mul_apply, Fin.sum_univ_six, pow_succ] <;> grind

theorem D_mul_A {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    glD hω * glA hω = glA hω * glD hω := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glD, glA, D6, A6, Matrix.mul_apply, Fin.sum_univ_six] <;> grind

theorem D_mul_P {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    glD hω * glP = glA hω * glP * glD hω := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glD, glA, glP, D6, A6, P6, Matrix.mul_apply, Fin.sum_univ_six] <;> grind

theorem F_conj_P {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * glP * (glF hω h2)⁻¹ = glA hω := by
  rw [F_mul_P hω h2]
  group

theorem F_conj_A {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * glA hω * (glF hω h2)⁻¹ = glP ^ 2 := by
  rw [F_mul_A hω h2]
  group

theorem D_conj_A {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    glD hω * glA hω * (glD hω)⁻¹ = glA hω := by
  rw [D_mul_A hω]
  group

theorem D_conj_P {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    glD hω * glP * (glD hω)⁻¹ = glA hω * glP := by
  rw [D_mul_P hω]
  group

theorem F_mul_B {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * B hω = B hω * glF hω h2 := by
  apply Units.ext
  change (glF hω h2 : Matrix (Fin 6) (Fin 6) K) * (B hω : Matrix (Fin 6) (Fin 6) K) =
    (B hω : Matrix (Fin 6) (Fin 6) K) * (glF hω h2 : Matrix (Fin 6) (Fin 6) K)
  rw [B_eq_diag hω h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glF, F6, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_six] <;> grind

theorem D_mul_B {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glD hω * B hω = B hω * glD hω := by
  apply Units.ext
  change (glD hω : Matrix (Fin 6) (Fin 6) K) * (B hω : Matrix (Fin 6) (Fin 6) K) =
    (B hω : Matrix (Fin 6) (Fin 6) K) * (glD hω : Matrix (Fin 6) (Fin 6) K)
  rw [B_eq_diag hω h2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glD, D6, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_six] <;> grind

theorem F_conj_B {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glF hω h2 * B hω * (glF hω h2)⁻¹ = B hω := by
  rw [F_mul_B hω h2]
  group

theorem D_conj_B {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    glD hω * B hω * (glD hω)⁻¹ = B hω := by
  rw [D_mul_B hω h2]
  group

theorem two_eq_zero_of_card_four [Finite K] (hK : Nat.card K = 4) : (2 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hcard
  simpa using (CharP.cast_eq_zero K 2)

noncomputable def suA {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨glA hω, by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · change (A6 ω).det = 1
      exact A6_det hω
    · change ((A6 ω).map (· ^ 2))ᵀ * A6 ω = 1
      exact A6_unitary hω h2⟩

noncomputable def suP : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨glP, by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · change (P6).det = 1
      exact P6_det
    · change (((P6 : Matrix (Fin 6) (Fin 6) K)).map (· ^ 2))ᵀ *
        (P6 : Matrix (Fin 6) (Fin 6) K) = 1
      exact P6_unitary⟩

noncomputable def suF {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨glF hω h2, by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · change (F6 ω).det = 1
      exact det_F6 hω h2
    · change ((F6 ω).map (· ^ 2))ᵀ * F6 ω = 1
      exact F6_unitary hω h2⟩

noncomputable def suD {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨glD hω, by
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · change (D6 ω).det = 1
      exact D6_det hω
    · change ((D6 ω).map (· ^ 2))ᵀ * D6 ω = 1
      exact D6_unitary hω h2⟩

noncomputable def proj : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _

noncomputable def a {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  proj (suA hω h2)

noncomputable def c :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  proj suP

noncomputable def f {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  proj (suF hω h2)

noncomputable def d {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  proj (suD hω h2)

noncomputable def suB {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⁅suA hω h2, suP⁆

theorem suF_conj_suP {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suF hω h2 * suP * (suF hω h2)⁻¹ = suA hω h2 := by
  apply Subtype.ext
  exact F_conj_P hω h2

theorem suF_conj_suA {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suF hω h2 * suA hω h2 * (suF hω h2)⁻¹ = suP ^ 2 := by
  apply Subtype.ext
  exact F_conj_A hω h2

theorem suD_conj_suA {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suD hω h2 * suA hω h2 * (suD hω h2)⁻¹ = suA hω h2 := by
  apply Subtype.ext
  exact D_conj_A hω

theorem suD_conj_suP {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suD hω h2 * suP * (suD hω h2)⁻¹ = suA hω h2 * suP := by
  apply Subtype.ext
  exact D_conj_P hω

theorem suF_conj_suB {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suF hω h2 * suB hω h2 * (suF hω h2)⁻¹ = suB hω h2 := by
  apply Subtype.ext
  change glF hω h2 * B hω * (glF hω h2)⁻¹ = B hω
  exact F_conj_B hω h2

theorem suD_conj_suB {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    suD hω h2 * suB hω h2 * (suD hω h2)⁻¹ = suB hω h2 := by
  apply Subtype.ext
  change glD hω * B hω * (glD hω)⁻¹ = B hω
  exact D_conj_B hω h2

theorem f_conj_c {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    f hω h2 * c * (f hω h2)⁻¹ = a hω h2 := by
  change proj (suF hω h2) * proj suP * (proj (suF hω h2))⁻¹ = proj (suA hω h2)
  simpa only [map_mul, map_inv] using congrArg proj (suF_conj_suP hω h2)

theorem f_conj_a {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    f hω h2 * a hω h2 * (f hω h2)⁻¹ = c ^ 2 := by
  change proj (suF hω h2) * proj (suA hω h2) * (proj (suF hω h2))⁻¹ = proj suP ^ 2
  simpa only [map_mul, map_inv, map_pow] using congrArg proj (suF_conj_suA hω h2)

theorem d_conj_a {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    d hω h2 * a hω h2 * (d hω h2)⁻¹ = a hω h2 := by
  change proj (suD hω h2) * proj (suA hω h2) * (proj (suD hω h2))⁻¹ = proj (suA hω h2)
  simpa only [map_mul, map_inv] using congrArg proj (suD_conj_suA hω h2)

theorem d_conj_c {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    d hω h2 * c * (d hω h2)⁻¹ = a hω h2 * c := by
  change proj (suD hω h2) * proj suP * (proj (suD hω h2))⁻¹ =
    proj (suA hω h2) * proj suP
  simpa only [map_mul, map_inv] using congrArg proj (suD_conj_suP hω h2)

theorem proj_suB {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    proj (suB hω h2) = ⁅a hω h2, c⁆ := by
  change proj ⁅suA hω h2, suP⁆ = ⁅proj (suA hω h2), proj suP⁆
  rw [map_commutatorElement]

theorem f_conj_b {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    f hω h2 * ⁅a hω h2, c⁆ * (f hω h2)⁻¹ = ⁅a hω h2, c⁆ := by
  change proj (suF hω h2) * proj (suB hω h2) * (proj (suF hω h2))⁻¹ =
    proj (suB hω h2)
  simpa only [map_mul, map_inv, proj_suB hω h2] using
    congrArg proj (suF_conj_suB hω h2)

theorem d_conj_b {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    d hω h2 * ⁅a hω h2, c⁆ * (d hω h2)⁻¹ = ⁅a hω h2, c⁆ := by
  change proj (suD hω h2) * proj (suB hω h2) * (proj (suD hω h2))⁻¹ =
    proj (suB hω h2)
  simpa only [map_mul, map_inv, proj_suB hω h2] using
    congrArg proj (suD_conj_suB hω h2)

theorem suA_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (suA hω h2) ^ 3 = 1 := by
  apply Subtype.ext
  exact glA_cube hω

theorem suP_cube : (suP : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ^ 3 = 1 := by
  apply Subtype.ext
  exact glP_cube

theorem suAP_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (suA hω h2 * suP) ^ 3 = 1 := by
  apply Subtype.ext
  exact AP_cube hω

theorem suAPinv_cube {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (suA hω h2 * suP⁻¹) ^ 3 = 1 := by
  apply Subtype.ext
  change (glA hω * (glP)⁻¹) ^ 3 = 1
  rw [glP_inv]
  exact APinv_cube hω

theorem cubeRel_su {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    CubeRel (suA hω h2) suP :=
  ⟨suA_cube hω h2, suP_cube, suAP_cube hω h2, suAPinv_cube hω h2⟩

theorem cubeRel_map {Γ Δ : Type*} [Group Γ] [Group Δ] {x y : Γ}
    (h : CubeRel x y) (f : Γ →* Δ) : CubeRel (f x) (f y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_pow, map_one] using congrArg f h.cube_left
  · simpa only [map_pow, map_one] using congrArg f h.cube_right
  · simpa only [map_mul, map_pow, map_one] using congrArg f h.cube_mul
  · simpa only [map_mul, map_inv, map_pow, map_one] using congrArg f h.cube_mul_inv

theorem cubeRel_a_c {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    CubeRel (a hω h2) c :=
  cubeRel_map (cubeRel_su hω h2) proj

theorem proj_eq_one_iff {x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))} :
    proj x = 1 ↔ (x : GL (Fin 6) K) ∈ LargeEvenScalars (Fin 6) K := by
  change (x : (↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ⧸
    (LargeEvenScalars (Fin 6) K).subgroupOf
      (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff x]
  rfl

theorem suB_not_scalar {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    (suB hω h2 : GL (Fin 6) K) ∉ LargeEvenScalars (Fin 6) K := by
  intro hmem
  rw [largeEvenScalars_def] at hmem
  obtain ⟨c₀, hc₀⟩ := hmem
  have hmat : ((suB hω h2 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.diagonal ![ω, ω, ω, 1, 1, 1] := by
    change (B hω : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal ![ω, ω, ω, 1, 1, 1]
    exact B_eq_diag hω h2
  have hscalar : ((suB hω h2 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      Matrix.scalar (Fin 6) (c₀ : K) := by
    rw [← hc₀]
    rfl
  have h00 : ω = (c₀ : K) := by
    have h := congrFun (congrFun (hmat.symm.trans hscalar) 0) 0
    simpa [Matrix.diagonal, Matrix.scalar] using h
  have h55 : (1 : K) = (c₀ : K) := by
    have h := congrFun (congrFun (hmat.symm.trans hscalar) 5) 5
    simpa [Matrix.diagonal, Matrix.scalar] using h
  exact omega_ne_one hω h2 (h00.trans h55.symm)

theorem proj_suB_ne_one {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    proj (suB hω h2) ≠ 1 := by
  intro h
  exact suB_not_scalar hω h2 (proj_eq_one_iff.mp h)

@[expose] def threeAMatrixAux (ω : K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.diagonal ![ω, ω ^ 2, 1, 1, 1, 1]

@[expose] noncomputable def threeASUAux {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (threeAMatrixAux ω) (by
      have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
      have hdet : (threeAMatrixAux ω).det = 1 := by
        simp [threeAMatrixAux, Matrix.det_diagonal, Fin.prod_univ_six]
        rw [show ω * ω ^ 2 = ω ^ 3 by ring, h3]
      rw [hdet]; exact one_ne_zero), by
      have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · have hdet : (threeAMatrixAux ω).det = 1 := by
          simp [threeAMatrixAux, Matrix.det_diagonal, Fin.prod_univ_six]
          rw [show ω * ω ^ 2 = ω ^ 3 by ring, h3]
        exact hdet
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [threeAMatrixAux, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;> grind⟩

@[expose] noncomputable def threeAAux {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _ (threeASUAux hω)

theorem threeASUAux_eq_mul {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    threeASUAux hω = suA hω h2 * suB hω h2 := by
  apply Subtype.ext
  apply Units.ext
  change threeAMatrixAux ω = A6 ω * B hω
  rw [B_eq_diag hω h2]
  have h3 : ω ^ 3 = 1 := by grind
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeAMatrixAux, A6, Matrix.mul_apply, Fin.sum_univ_six, Matrix.diagonal] <;> grind

theorem threeAAux_eq_mul {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    threeAAux hω = a hω h2 * ⁅a hω h2, c⁆ := by
  calc
    threeAAux hω = proj (threeASUAux hω) := rfl
    _ = proj (suA hω h2 * suB hω h2) :=
      congrArg proj (threeASUAux_eq_mul hω h2)
    _ = proj (suA hω h2) * proj (suB hω h2) := map_mul proj _ _
    _ = a hω h2 * ⁅a hω h2, c⁆ := by rw [proj_suB]; rfl

noncomputable def heisSetup {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h2 : (2 : K) = 0) :
    Abs.HeisSetup (Γ := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) where
  a := a hω h2
  c := c
  f := f hω h2
  d := d hω h2
  hcr := cubeRel_a_c hω h2
  hfc := f_conj_c hω h2
  hfa := f_conj_a hω h2
  hda := d_conj_a hω h2
  hdc := d_conj_c hω h2
  hfb := f_conj_b hω h2
  hdb := d_conj_b hω h2
  hbne := by
    rw [← proj_suB hω h2]
    exact proj_suB_ne_one hω h2

theorem exists_extraspecial_conj_threeAAux [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ (P : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))))
      (z : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))),
      Nat.card P = 27 ∧ (∀ g ∈ P, g ^ 3 = 1) ∧ z ∈ P ∧ (∀ g ∈ P, g * z = z * g) ∧
      ∀ g ∈ P, g ∉ Subgroup.zpowers z →
        ∃ u : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)),
          u * threeAAux hω * u⁻¹ = g ∨ u * (threeAAux hω)⁻¹ * u⁻¹ = g := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let h2 : (2 : K) = 0 := two_eq_zero_of_card_four hK
  let S : Abs.HeisSetup (Γ := LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    heisSetup hω h2
  let P : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    Subgroup.closure ({S.a, S.c} : Set _)
  refine ⟨P, S.b, S.card_closure, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact S.hcr.pow_three_eq_one hg
  · change S.b ∈ P
    exact Subgroup.commutator_le_self P
      (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
  · intro g hg
    have hle : P ≤ Subgroup.centralizer ({S.b} : Set _) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · change S.a ∈ Subgroup.centralizer ({S.b} : Set _)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        simp only [Set.mem_singleton_iff] at hh
        subst hh
        exact S.hcr.commute_commutator_left
      · change S.c ∈ Subgroup.centralizer ({S.b} : Set _)
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        simp only [Set.mem_singleton_iff] at hh
        subst hh
        exact S.hcr.commute_commutator_right
    exact ((Subgroup.mem_centralizer_iff.mp (hle hg)) S.b (by simp)).symm
  · intro g hg hgz
    have hR : ∃ u, u * (S.a * S.b) * u⁻¹ = g := S.mem_closure_conj hg hgz
    rcases hR with ⟨u, hu⟩
    refine ⟨u, Or.inl ?_⟩
    rw [threeAAux_eq_mul hω h2]
    exact hu

end CFSG.StandardType.USixTwo.Extraspecial

end
