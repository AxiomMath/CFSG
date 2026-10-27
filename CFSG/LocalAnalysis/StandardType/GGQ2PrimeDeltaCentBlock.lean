module

public import CFSG.Fischer.Unitary
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartOne.KP.Fi22Unitary
import CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Matrix CFSG.Fischer CFSG.Open

@[expose] def deltaCentBlockMat (A : Matrix (Fin 5) (Fin 5) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (A i') j) i

private theorem deltaCentBlockMat_succ_succ (A : Matrix (Fin 5) (Fin 5) F4) (i j : Fin 5) :
    deltaCentBlockMat A i.succ j.succ = A i j := rfl

private theorem deltaCentBlockMat_zero_succ (A : Matrix (Fin 5) (Fin 5) F4) (j : Fin 5) :
    deltaCentBlockMat A 0 j.succ = 0 := rfl

private theorem deltaCentBlockMat_succ_zero (A : Matrix (Fin 5) (Fin 5) F4) (i : Fin 5) :
    deltaCentBlockMat A i.succ 0 = 0 := rfl

private theorem deltaCentBlockMat_zero_zero (A : Matrix (Fin 5) (Fin 5) F4) :
    deltaCentBlockMat A 0 0 = 1 := rfl

private theorem deltaCentExt {M N : Matrix (Fin 6) (Fin 6) F4} (h00 : M 0 0 = N 0 0)
    (h0s : ∀ j : Fin 5, M 0 j.succ = N 0 j.succ) (hs0 : ∀ i : Fin 5, M i.succ 0 = N i.succ 0)
    (hss : ∀ i j : Fin 5, M i.succ j.succ = N i.succ j.succ) : M = N := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  exacts [h00, h0s j, hs0 i, hss i j]

private def deltaCentBlock : Matrix (Fin 5) (Fin 5) F4 →* Matrix (Fin 6) (Fin 6) F4 where
  toFun := deltaCentBlockMat
  map_one' := deltaCentExt rfl
    (fun j => by simp [deltaCentBlockMat_zero_succ, one_apply, (Fin.succ_ne_zero j).symm])
    (fun i => by simp [deltaCentBlockMat_succ_zero, one_apply, Fin.succ_ne_zero i])
    (fun i j => by simp [deltaCentBlockMat_succ_succ, one_apply])
  map_mul' A B := deltaCentExt (by simp [deltaCentBlockMat_zero_zero, mul_apply, Fin.sum_univ_succ,
      deltaCentBlockMat_zero_succ, deltaCentBlockMat_succ_zero])
    (fun j => by simp [deltaCentBlockMat_zero_succ, mul_apply, Fin.sum_univ_succ,
      deltaCentBlockMat_zero_succ, deltaCentBlockMat_zero_zero])
    (fun i => by simp [deltaCentBlockMat_succ_zero, mul_apply, Fin.sum_univ_succ,
      deltaCentBlockMat_zero_zero])
    (fun i j => by simp [deltaCentBlockMat_succ_succ, mul_apply, Fin.sum_univ_succ,
      deltaCentBlockMat_succ_zero, deltaCentBlockMat_zero_succ])

private theorem deltaCentBlockMat_transpose (A : Matrix (Fin 5) (Fin 5) F4) :
    deltaCentBlockMat Aᵀ = (deltaCentBlockMat A)ᵀ :=
  deltaCentExt rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)

private theorem deltaCentBlockMat_map_sq (A : Matrix (Fin 5) (Fin 5) F4) :
    deltaCentBlockMat (A.map (· ^ 2)) = (deltaCentBlockMat A).map (· ^ 2) :=
  deltaCentExt (by simp [deltaCentBlockMat_zero_zero])
    (fun j => by simp [deltaCentBlockMat_zero_succ])
    (fun i => by simp [deltaCentBlockMat_succ_zero]) (fun _ _ => rfl)

private theorem deltaCentBlock_apply (A : Matrix (Fin 5) (Fin 5) F4) :
    deltaCentBlock A = deltaCentBlockMat A := rfl

private theorem det_deltaCentBlock (A : Matrix (Fin 5) (Fin 5) F4) :
    (deltaCentBlock A).det = A.det := by
  have h : (deltaCentBlockMat A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [deltaCentBlock_apply, deltaCentBlockMat_zero_zero, deltaCentBlockMat_zero_succ,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero, h]

private theorem deltaCentBlock_injective : Function.Injective deltaCentBlock := by
  intro A B h
  ext i j
  exact congrFun (congrFun h i.succ) j.succ

def deltaCentBlockGL : GL (Fin 5) F4 →* GL (Fin 6) F4 := Units.map deltaCentBlock

private theorem deltaCentBlockGL_val_aux (A : GL (Fin 5) F4) :
    ((deltaCentBlockGL A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      deltaCentBlockMat (A : Matrix (Fin 5) (Fin 5) F4) := rfl

theorem deltaCentBlockGL_val (A : GL (Fin 5) F4) :
    ((deltaCentBlockGL A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      deltaCentBlockMat (A : Matrix (Fin 5) (Fin 5) F4) := deltaCentBlockGL_val_aux A

theorem deltaCentBlockGL_apply_zero_zero (A : GL (Fin 5) F4) :
    ((deltaCentBlockGL A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) 0 0 = 1 := by
  rw [deltaCentBlockGL_val]
  exact deltaCentBlockMat_zero_zero _

theorem deltaCentBlockGL_det (A : GL (Fin 5) F4) :
    Matrix.GeneralLinearGroup.det (deltaCentBlockGL A) = Matrix.GeneralLinearGroup.det A := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    deltaCentBlockGL_val, ← deltaCentBlock_apply]
  exact det_deltaCentBlock _

theorem deltaCentBlockGL_injective : Function.Injective deltaCentBlockGL :=
  Units.map_injective deltaCentBlock_injective

theorem deltaCentBlockMat_comm_diagonal (A : Matrix (Fin 5) (Fin 5) F4) (a : F4) :
    deltaCentBlockMat A * Matrix.diagonal (fun i : Fin 6 => if i = 0 then a else 1) =
      Matrix.diagonal (fun i : Fin 6 => if i = 0 then a else 1) * deltaCentBlockMat A := by
  refine deltaCentExt ?_ (fun j => ?_) (fun i => ?_) (fun i j => ?_) <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, deltaCentBlockMat_zero_zero,
      deltaCentBlockMat_zero_succ, deltaCentBlockMat_succ_zero, deltaCentBlockMat_succ_succ,
      Fin.succ_ne_zero, mul_comm]

theorem deltaCentBlockGL_mem_SU0 {A : GL (Fin 5) F4} (hA : A ∈ StatedSU 5 (2 ^ 1) F4) :
    deltaCentBlockGL A ∈ SU0 := by
  have hle : StatedSU 5 (2 ^ 1) F4 ≤ SU0.comap deltaCentBlockGL := by
    unfold StatedSU
    rw [Subgroup.closure_le]
    rintro B ⟨hdet, hform⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, mem_SU0]
    refine ⟨Units.ext ?_, CFSG.RankThree.PartOne.isIsom_iff_stated.2 ?_⟩
    · rw [Matrix.GeneralLinearGroup.val_det_apply, deltaCentBlockGL_val, ← deltaCentBlock_apply,
        det_deltaCentBlock, hdet]
      rfl
    · have h1 : ((B : Matrix (Fin 5) (Fin 5) F4).map (· ^ 2))ᵀ * (B : Matrix (Fin 5) (Fin 5) F4) =
          1 := by simpa using hform
      rw [deltaCentBlockGL_val, ← deltaCentBlockMat_map_sq, ← deltaCentBlockMat_transpose]
      simp only [← deltaCentBlock_apply, ← map_mul, h1, map_one]
  exact hle hA

theorem exists_deltaCentBlock_of_block_shape {g : GL (Fin 6) F4} (hg : g ∈ SU0)
    (h0 : ∀ i : Fin 5, (g : Matrix (Fin 6) (Fin 6) F4) i.succ 0 = 0)
    (h1 : ∀ j : Fin 5, (g : Matrix (Fin 6) (Fin 6) F4) 0 j.succ = 0) :
    ∃ (s : F4ˣ) (A : GL (Fin 5) F4), A ∈ StatedSU 5 (2 ^ 1) F4 ∧
      g * scalarGL s = deltaCentBlockGL A := by
  obtain ⟨-, hisom⟩ := mem_SU0.1 hg
  have ha : (g : Matrix (Fin 6) (Fin 6) F4) 0 0 ^ 2 * (g : Matrix (Fin 6) (Fin 6) F4) 0 0 = 1 := by
    have := congrFun (congrFun (CFSG.RankThree.PartOne.isIsom_iff_stated.1 hisom) 0) 0
    simpa [mul_apply, Fin.sum_univ_succ, h0] using this
  let s : F4ˣ := ⟨(g : Matrix (Fin 6) (Fin 6) F4) 0 0 ^ 2, (g : Matrix (Fin 6) (Fin 6) F4) 0 0,
    ha, by rw [mul_comm]; exact ha⟩
  have hg' : g * scalarGL s ∈ SU0 := SU0.mul_mem hg (scalarGL_mem s)
  have hval : ((g * scalarGL s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      (s : F4) • (g : Matrix (Fin 6) (Fin 6) F4) := by
    rw [Units.val_mul, scalarGL_val, Matrix.mul_smul, Matrix.mul_one]
  obtain ⟨hdet', hisom'⟩ := mem_SU0.1 hg'
  have hshape : ((g * scalarGL s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      deltaCentBlockMat (((g * scalarGL s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).submatrix
        Fin.succ Fin.succ) := by
    refine deltaCentExt ?_ (fun j => ?_) (fun i => ?_) (fun i j => rfl)
    · rw [deltaCentBlockMat_zero_zero, hval, Matrix.smul_apply, smul_eq_mul]
      exact ha
    · rw [deltaCentBlockMat_zero_succ, hval, Matrix.smul_apply, h1 j, smul_zero]
    · rw [deltaCentBlockMat_succ_zero, hval, Matrix.smul_apply, h0 i, smul_zero]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin 5) (Fin 5) F4,
      ((g * scalarGL s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = deltaCentBlockMat B :=
    ⟨_, hshape⟩
  have hdetB : B.det = 1 := by
    have := congrArg Units.val hdet'
    rw [Matrix.GeneralLinearGroup.val_det_apply, hB, ← deltaCentBlock_apply,
      det_deltaCentBlock] at this
    exact this
  have hformB : (B.map (· ^ 2))ᵀ * B = 1 := by
    have h := CFSG.RankThree.PartOne.isIsom_iff_stated.1 hisom'
    rw [hB, ← deltaCentBlockMat_map_sq, ← deltaCentBlockMat_transpose] at h
    simp only [← deltaCentBlock_apply, ← map_mul, ← map_one deltaCentBlock] at h
    exact deltaCentBlock_injective h
  have hAval := Matrix.GeneralLinearGroup.val_mkOfDetNeZero B (by rw [hdetB]; exact one_ne_zero)
  refine ⟨s, Matrix.GeneralLinearGroup.mkOfDetNeZero B (by rw [hdetB]; exact one_ne_zero),
    ?_, Units.ext ?_⟩
  · unfold StatedSU
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [hAval]
      exact hdetB
    · rw [hAval]
      exact hformB
  · rw [deltaCentBlockGL_val, hAval, hB]

end CFSG.GGQ2Prime
