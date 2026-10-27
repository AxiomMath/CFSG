module

public import CFSG.LocalAnalysis.WeakClosure81.Orth6Minus.Defs
import CFSG.ClassicalGroups.Orthogonal.SumSquares

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Orth6Minus

open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

private abbrev Z3 := ZMod 3

private def coordInv : Six → Fin 6
  | Sum.inl a => if a = 0 then 0 else 1
  | Sum.inr (Sum.inl a) => if a = 0 then 2 else 3
  | Sum.inr (Sum.inr a) => if a = 0 then 4 else 5

private def coordEquiv : Fin 6 ≃ Six where
  toFun := coord
  invFun := coordInv
  left_inv := by decide
  right_inv := by decide

private noncomputable def cast3 (K : Type*) [Field K] [CharP K 3] : Z3 →+* K :=
  ZMod.castHom (dvd_refl 3) K

private noncomputable def toK {K : Type*} [Field K] [CharP K 3]
    (M : Matrix (Fin 6) (Fin 6) Z3) : Matrix Six Six K :=
  Matrix.reindex coordEquiv coordEquiv (M.map (cast3 K))

private lemma toK_mul {K : Type*} [Field K] [CharP K 3]
    (M N : Matrix (Fin 6) (Fin 6) Z3) :
    toK (M * N) = toK (K := K) M * toK (K := K) N := by
  rw [toK, toK, toK, Matrix.map_mul, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul _ _ _ coordEquiv.symm _
      coordEquiv.symm.bijective]

private lemma toK_one {K : Type*} [Field K] [CharP K 3] :
    toK (K := K) 1 = 1 := by
  rw [toK, Matrix.map_one _ (map_zero _) (map_one _), Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

private lemma toK_transpose {K : Type*} [Field K] [CharP K 3]
    (M : Matrix (Fin 6) (Fin 6) Z3) :
    (toK (K := K) M).transpose = toK (K := K) M.transpose := by
  rw [toK, toK, Matrix.transpose_reindex, ← Matrix.transpose_map]

private lemma toK_diag {K : Type*} [Field K] [CharP K 3] (d : Fin 6 → Z3) :
    toK (K := K) (Matrix.diagonal d) =
      Matrix.diagonal (fun i => cast3 K (d (coordEquiv.symm i))) := by
  rw [toK, Matrix.reindex_apply, Matrix.diagonal_map (map_zero _),
    Matrix.submatrix_diagonal _ _ coordEquiv.symm.injective]
  rfl

private def dT3 : Fin 6 → Z3 := ![2, 2, 1, 1, 1, 1]
private def dN3 : Fin 6 → Z3 := ![1, 1, 1, 1, 2, 2]
private def dD3 : Fin 6 → Z3 := ![2, 2, 2, 2, 1, 1]
private def T3 : Matrix (Fin 6) (Fin 6) Z3 := Matrix.diagonal dT3
private def N3 : Matrix (Fin 6) (Fin 6) Z3 := Matrix.diagonal dN3
private def D3 : Matrix (Fin 6) (Fin 6) Z3 := Matrix.diagonal dD3

private def H3 : Matrix (Fin 6) (Fin 6) Z3 :=
  !![1, 1, 1, 1, 0, 0;
     1, -1, 1, -1, 0, 0;
     1, 1, -1, -1, 0, 0;
     1, -1, -1, 1, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private def W3 : Matrix (Fin 6) (Fin 6) Z3 :=
  !![0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0]

private lemma H3_sq : H3 * H3 = 1 := by decide +kernel
private lemma H3_transpose : H3.transpose = H3 := by decide +kernel
private lemma W3_sq : W3 * W3 = 1 := by decide +kernel
private lemma W3_transpose_mul : W3.transpose * W3 = 1 := by decide +kernel
private lemma W3_T3_W3 : W3 * T3 * W3 = N3 := by decide +kernel
private lemma H3_N3 : H3 * N3 = N3 * H3 := by decide +kernel
private lemma X3_sq : (T3 * H3 * T3 * H3) * (T3 * H3 * T3 * H3) = D3 := by
  decide +kernel
private lemma N3_sq : N3 * N3 = 1 := by decide +kernel
private lemma D3_sq : D3 * D3 = 1 := by decide +kernel

private lemma cast3_two {K : Type*} [Field K] [CharP K 3] :
    (ZMod.cast (2 : Z3) : K) = -1 := by
  have h2 : (2 : K) = -1 := by
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    linear_combination h3
  rw [show (ZMod.cast (2 : Z3) : K) = (2 : K) from rfl, h2]

private lemma toK_T3 {K : Type*} [Field K] [CharP K 3] :
    toK (K := K) T3 = tGL K := by
  rw [T3, toK_diag, tGL, negCoordGL, TauCeti.diagGL_coe]
  congr 1
  funext i
  obtain ⟨a, rfl⟩ := coordEquiv.surjective i
  fin_cases a <;> simp [dT3, coord, coordEquiv, coordInv, cast3, cast3_two,
    Finset.mem_insert, Finset.mem_singleton]

private lemma toK_D3 {K : Type*} [Field K] [CharP K 3] :
    toK (K := K) D3 = negCoordGL (K := K) {coord 0, coord 1, coord 2, coord 3} := by
  rw [D3, toK_diag, negCoordGL, TauCeti.diagGL_coe]
  congr 1
  funext i
  obtain ⟨a, rfl⟩ := coordEquiv.surjective i
  fin_cases a <;> simp [dD3, coord, coordEquiv, coordInv, cast3, cast3_two,
    Finset.mem_insert, Finset.mem_singleton]

private noncomputable def Hsix (K : Type*) [Field K] [CharP K 3] : GL Six K where
  val := toK (K := K) H3
  inv := toK (K := K) H3
  val_inv := by rw [← toK_mul, H3_sq, toK_one]
  inv_val := by rw [← toK_mul, H3_sq, toK_one]

private noncomputable def Wsix (K : Type*) [Field K] [CharP K 3] : GL Six K where
  val := toK (K := K) W3
  inv := toK (K := K) W3
  val_inv := by rw [← toK_mul, W3_sq, toK_one]
  inv_val := by rw [← toK_mul, W3_sq, toK_one]

private noncomputable def Nsix (K : Type*) [Field K] [CharP K 3] : GL Six K where
  val := toK (K := K) N3
  inv := toK (K := K) N3
  val_inv := by rw [← toK_mul, N3_sq, toK_one]
  inv_val := by rw [← toK_mul, N3_sq, toK_one]

private noncomputable def Dsix (K : Type*) [Field K] : GL Six K :=
  negCoordGL (K := K) {coord 0, coord 1, coord 2, coord 3}

private noncomputable def gsix (K : Type*) [Field K] [CharP K 3] : GL Six K :=
  ⁅Hsix K, Wsix K⁆

private noncomputable def Xsix (K : Type*) [Field K] [CharP K 3] : GL Six K :=
  tGL K * Hsix K * tGL K * Hsix K

private noncomputable def xsix (K : Type*) [Field K] [CharP K 3] : GL Six K :=
  tGL K * (gsix K * tGL K * (gsix K)⁻¹)

private lemma Hsix_sq {K : Type*} [Field K] [CharP K 3] : Hsix K * Hsix K = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one]
  change toK (K := K) H3 * toK (K := K) H3 = 1
  rw [← toK_mul, H3_sq, toK_one]

private lemma Wsix_sq {K : Type*} [Field K] [CharP K 3] : Wsix K * Wsix K = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one]
  change toK (K := K) W3 * toK (K := K) W3 = 1
  rw [← toK_mul, W3_sq, toK_one]

private lemma Dsix_sq {K : Type*} [Field K] [CharP K 3] : Dsix K * Dsix K = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one]
  dsimp [Dsix]
  rw [← toK_D3, ← toK_mul, D3_sq, toK_one]

private lemma Hsix_transpose_mul {K : Type*} [Field K] [CharP K 3] :
    (Hsix K : Matrix Six Six K).transpose * Hsix K = 1 := by
  change (toK (K := K) H3).transpose * toK (K := K) H3 = 1
  rw [toK_transpose, ← toK_mul, H3_transpose, H3_sq, toK_one]

private lemma Wsix_transpose_mul {K : Type*} [Field K] [CharP K 3] :
    (Wsix K : Matrix Six Six K).transpose * Wsix K = 1 := by
  change (toK (K := K) W3).transpose * toK (K := K) W3 = 1
  rw [toK_transpose, ← toK_mul, W3_transpose_mul, toK_one]

private lemma Hsix_mem {K : Type*} [Field K] [CharP K 3] : Hsix K ∈ orthSix K :=
  mem_orthogonalGroup_sumSqForm_of_transpose_mul_self (Hsix_transpose_mul (K := K))

private lemma Wsix_mem {K : Type*} [Field K] [CharP K 3] : Wsix K ∈ orthSix K :=
  mem_orthogonalGroup_sumSqForm_of_transpose_mul_self (Wsix_transpose_mul (K := K))

private lemma gsix_mem {K : Type*} [Field K] [CharP K 3] :
    gsix K ∈ ⁅orthSix K, orthSix K⁆ :=
  Subgroup.commutator_mem_commutator (Hsix_mem (K := K)) (Wsix_mem (K := K))

private lemma Wsix_tGL_Wsix {K : Type*} [Field K] [CharP K 3] :
    Wsix K * tGL K * Wsix K = Nsix K := by
  apply Units.ext
  simp only [Units.val_mul]
  dsimp [Wsix, Nsix]
  rw [← toK_T3, ← toK_mul, ← toK_mul, W3_T3_W3]

private lemma Hsix_Nsix {K : Type*} [Field K] [CharP K 3] :
    Hsix K * Nsix K = Nsix K * Hsix K := by
  apply Units.ext
  simp only [Units.val_mul]
  dsimp [Hsix, Nsix]
  rw [← toK_mul, ← toK_mul, H3_N3]

private lemma Hsix_Nsix_Hsix {K : Type*} [Field K] [CharP K 3] :
    Hsix K * Nsix K * Hsix K = Nsix K := by
  rw [Hsix_Nsix, mul_assoc, Hsix_sq, mul_one]

private lemma Wsix_Nsix_Wsix {K : Type*} [Field K] [CharP K 3] :
    Wsix K * Nsix K * Wsix K = tGL K := by
  rw [← Wsix_tGL_Wsix]
  calc Wsix K * (Wsix K * tGL K * Wsix K) * Wsix K =
      (Wsix K * Wsix K) * tGL K * (Wsix K * Wsix K) := by group
    _ = tGL K := by rw [Wsix_sq, one_mul, mul_one]

private lemma gsix_eq {K : Type*} [Field K] [CharP K 3] :
    gsix K = Hsix K * Wsix K * Hsix K * Wsix K := by
  have hH : Hsix K = (Hsix K)⁻¹ := eq_inv_of_mul_eq_one_right (Hsix_sq (K := K))
  have hW : Wsix K = (Wsix K)⁻¹ := eq_inv_of_mul_eq_one_right (Wsix_sq (K := K))
  dsimp [gsix]
  rw [commutatorElement_def, ← hH, ← hW]

private lemma gsix_mul_inv {K : Type*} [Field K] [CharP K 3] :
    gsix K * (Wsix K * Hsix K * Wsix K * Hsix K) = 1 := by
  rw [gsix_eq]
  calc Hsix K * Wsix K * Hsix K * Wsix K * (Wsix K * Hsix K * Wsix K * Hsix K)
      = Hsix K * Wsix K * Hsix K * (Wsix K * Wsix K) * Hsix K * Wsix K * Hsix K := by
        group
    _ = Hsix K * Wsix K * Hsix K * 1 * Hsix K * Wsix K * Hsix K := by
        rw [Wsix_sq]
    _ = Hsix K * Wsix K * (Hsix K * Hsix K) * Wsix K * Hsix K := by group
    _ = Hsix K * Wsix K * 1 * Wsix K * Hsix K := by rw [Hsix_sq]
    _ = Hsix K * (Wsix K * Wsix K) * Hsix K := by group
    _ = Hsix K * 1 * Hsix K := by rw [Wsix_sq]
    _ = Hsix K * Hsix K := by rw [mul_one]
    _ = 1 := Hsix_sq

private lemma gsix_inv {K : Type*} [Field K] [CharP K 3] :
    (gsix K)⁻¹ = Wsix K * Hsix K * Wsix K * Hsix K :=
  (eq_inv_of_mul_eq_one_right (gsix_mul_inv (K := K))).symm

private lemma gsix_conj {K : Type*} [Field K] [CharP K 3] :
    gsix K * tGL K * (gsix K)⁻¹ = Hsix K * tGL K * Hsix K := by
  rw [gsix_inv, gsix_eq]
  calc Hsix K * Wsix K * Hsix K * Wsix K * tGL K * (Wsix K * Hsix K * Wsix K * Hsix K)
      = Hsix K * Wsix K * Hsix K * (Wsix K * tGL K * Wsix K) * Hsix K * Wsix K *
          Hsix K := by group
    _ = Hsix K * Wsix K * Hsix K * Nsix K * Hsix K * Wsix K * Hsix K := by
        rw [Wsix_tGL_Wsix]
    _ = Hsix K * Wsix K * (Hsix K * Nsix K * Hsix K) * Wsix K * Hsix K := by group
    _ = Hsix K * Wsix K * Nsix K * Wsix K * Hsix K := by rw [Hsix_Nsix_Hsix]
    _ = Hsix K * (Wsix K * Nsix K * Wsix K) * Hsix K := by group
    _ = Hsix K * tGL K * Hsix K := by rw [Wsix_Nsix_Wsix]

private lemma Xsix_sq {K : Type*} [Field K] [CharP K 3] : Xsix K * Xsix K = Dsix K := by
  apply Units.ext
  simp only [Units.val_mul]
  dsimp [Xsix, Hsix, Dsix]
  rw [← toK_T3, ← toK_D3]
  change toK (K := K) T3 * toK (K := K) H3 * toK (K := K) T3 *
      toK (K := K) H3 * (toK (K := K) T3 * toK (K := K) H3 *
      toK (K := K) T3 * toK (K := K) H3) = toK (K := K) D3
  repeat rw [← toK_mul]
  rw [X3_sq]

private lemma xsix_eq_X {K : Type*} [Field K] [CharP K 3] : xsix K = Xsix K := by
  dsimp [xsix, Xsix]
  rw [gsix_conj]
  group

private lemma xsix_sq {K : Type*} [Field K] [CharP K 3] : xsix K * xsix K = Dsix K := by
  rw [xsix_eq_X, Xsix_sq]

private lemma Dsix_not_center {K : Type*} [Field K] [CharP K 3] :
    Dsix K ∉ Subgroup.center (GL Six K) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  dsimp [Dsix]
  refine TauCeti.notMem_range_scalar_diagGL (i := coord 0) (j := coord 4) ?_
  have h0 : coord 0 ∈ ({coord 0, coord 1, coord 2, coord 3} : Finset Six) := by decide
  have h4 : coord 4 ∉ ({coord 0, coord 1, coord 2, coord 3} : Finset Six) := by decide
  rw [if_pos h0, if_neg h4]
  intro h
  have h2ne : (2 : K) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := K) (p := 3) (q := 2) Nat.prime_two (by decide)
  have hneg : (-1 : K) ≠ 1 := by
    intro h1
    apply h2ne
    linear_combination -h1
  exact hneg (by simpa using congrArg Units.val h)

private lemma xsix_order {K : Type*} [Field K] [CharP K 3] :
    orderOf (Matrix.ProjGenLinGroup.mk (xsix K)) = 4 := by
  have hx4 : xsix K ^ 4 = 1 := by
    have h44 : xsix K ^ 4 = (xsix K * xsix K) * (xsix K * xsix K) := by
      rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    rw [h44, xsix_sq, Dsix_sq]
  have hfin : (Matrix.ProjGenLinGroup.mk (xsix K)) ^ 4 = 1 := by
    rw [← map_pow, hx4, map_one]
  have hnot : (Matrix.ProjGenLinGroup.mk (xsix K)) ^ 2 ≠ 1 := by
    rw [← map_pow, show xsix K ^ 2 = Dsix K by rw [pow_two, xsix_sq]]
    intro h
    exact Dsix_not_center ((Matrix.ProjGenLinGroup.mk_eq_one).1 h)
  have h := orderOf_eq_prime_pow (x := Matrix.ProjGenLinGroup.mk (xsix K)) (p := 2) (n := 1)
    (hp := ⟨Nat.prime_two⟩) hnot hfin
  simpa using h

private theorem exists_mem_commutator_orderOf_eq_four_aux {K : Type*} [Field K]
    [CharP K 3] :
    ∃ h ∈ ⁅orthSix K, orthSix K⁆,
      orderOf (Matrix.ProjGenLinGroup.mk (tGL K) * (Matrix.ProjGenLinGroup.mk h *
        Matrix.ProjGenLinGroup.mk (tGL K) * (Matrix.ProjGenLinGroup.mk h)⁻¹)) = 4 := by
  refine ⟨gsix K, gsix_mem (K := K), ?_⟩
  have hgoal : Matrix.ProjGenLinGroup.mk (tGL K) *
      (Matrix.ProjGenLinGroup.mk (gsix K) * Matrix.ProjGenLinGroup.mk (tGL K) *
        (Matrix.ProjGenLinGroup.mk (gsix K))⁻¹) = Matrix.ProjGenLinGroup.mk (xsix K) := by
    simp [xsix]
  rw [hgoal, xsix_order (K := K)]

theorem exists_mem_commutator_orderOf_eq_four {K : Type*} [Field K] (h3 : (3 : K) = 0) :
    ∃ h ∈ ⁅orthSix K, orthSix K⁆,
      orderOf (Matrix.ProjGenLinGroup.mk (tGL K) * (Matrix.ProjGenLinGroup.mk h *
        Matrix.ProjGenLinGroup.mk (tGL K) * (Matrix.ProjGenLinGroup.mk h)⁻¹)) = 4 :=
  @exists_mem_commutator_orderOf_eq_four_aux K _
    ((CharP.charP_iff_prime_eq_zero (by decide)).2 h3)

end CFSG.LocalAnalysis.WeakClosure81.Orth6Minus
