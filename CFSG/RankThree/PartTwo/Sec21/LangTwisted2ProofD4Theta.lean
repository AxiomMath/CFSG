module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Ops

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {L : Type} [Field L]

@[expose] def secTh0 (μ : L) : Fin 3 → Fin 3 → RootModule TwistTag.D4.tag L :=
  ![![hVec TwistTag.D4.tag L 0 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 2 +
        hVec TwistTag.D4.tag L 3,
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) + μ • rootVec TwistTag.D4.tag L (dv 0 1 0 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 0 1),
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) + rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        rootVec TwistTag.D4.tag L (dv 1 1 1 0)],
    ![rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)),
      hVec TwistTag.D4.tag L 2,
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) + μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 0 1 1)],
    ![rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0),
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)),
      hVec TwistTag.D4.tag L 0 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 3]]

@[expose] def secTh1 (μ : L) : Fin 3 → Fin 3 → RootModule TwistTag.D4.tag L :=
  ![![hVec TwistTag.D4.tag L 0 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 3,
      rootVec TwistTag.D4.tag L (dv 1 0 1 0) + μ • rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 1 1),
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) + rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        rootVec TwistTag.D4.tag L (dv 1 1 1 0)],
    ![rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)),
      hVec TwistTag.D4.tag L 2,
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) + μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 1 0 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 0 0 1)],
    ![rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0),
      rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) + μ • rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)),
      hVec TwistTag.D4.tag L 0 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 3 +
        hVec TwistTag.D4.tag L 2]]

@[expose] def secTh2 (μ : L) : Fin 3 → Fin 3 → RootModule TwistTag.D4.tag L :=
  ![![hVec TwistTag.D4.tag L 2,
      rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) 0) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 0 (-1) (-1)),
      rootVec TwistTag.D4.tag L (dv 1 0 0 0) + rootVec TwistTag.D4.tag L (dv 0 1 0 0) +
        rootVec TwistTag.D4.tag L (dv 0 0 0 1)],
    ![rootVec TwistTag.D4.tag L (dv 1 0 1 0) + μ ^ 2 • rootVec TwistTag.D4.tag L (dv 0 1 1 0) +
        μ • rootVec TwistTag.D4.tag L (dv 0 0 1 1),
      hVec TwistTag.D4.tag L 3 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 0,
      rootVec TwistTag.D4.tag L (dv 0 1 1 1) + μ ^ 2 • rootVec TwistTag.D4.tag L (dv 1 0 1 1) +
        μ • rootVec TwistTag.D4.tag L (dv 1 1 1 0)],
    ![rootVec TwistTag.D4.tag L (dv (-1) 0 0 0) + rootVec TwistTag.D4.tag L (dv 0 (-1) 0 0) +
        rootVec TwistTag.D4.tag L (dv 0 0 0 (-1)),
      rootVec TwistTag.D4.tag L (dv 0 (-1) (-1) (-1)) +
        μ • rootVec TwistTag.D4.tag L (dv (-1) 0 (-1) (-1)) +
        μ ^ 2 • rootVec TwistTag.D4.tag L (dv (-1) (-1) (-1) 0),
      hVec TwistTag.D4.tag L 0 + hVec TwistTag.D4.tag L 1 + hVec TwistTag.D4.tag L 3 +
        hVec TwistTag.D4.tag L 2]]

@[expose] def secTh (μ : L) (j : Fin 3) : Fin 3 → Fin 3 → RootModule TwistTag.D4.tag L :=
  ![secTh0 μ, secTh1 μ, secTh2 μ] j

@[expose] def secThL (μ : L) (j : Fin 3) :
    Matrix (Fin 3) (Fin 3) L →ₗ[L] RootModule TwistTag.D4.tag L where
  toFun X := ∑ a, ∑ b, X a b • secTh μ j a b
  map_add' X Y := by
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem secThL_apply (μ : L) (j : Fin 3) (X : Matrix (Fin 3) (Fin 3) L) :
    secThL μ j X = ∑ a, ∑ b, X a b • secTh μ j a b := rfl

theorem secThL_single (μ : L) (j a b : Fin 3) :
    secThL μ j (Matrix.single a b 1) = secTh μ j a b := by
  rw [secThL_apply]
  simp only [Matrix.single_apply, ite_smul, one_smul, zero_smul, ite_and]
  simp [Finset.sum_ite_eq]

theorem secThL_conj_of_single (μ : L) {j j' : Fin 3}
    (f : Module.End L (RootModule TwistTag.D4.tag L)) (G G' : Matrix (Fin 3) (Fin 3) L)
    (h : ∀ a b, f (secTh μ j a b) = secThL μ j' (G * Matrix.single a b 1 * G'))
    (X : Matrix (Fin 3) (Fin 3) L) : f (secThL μ j X) = secThL μ j' (G * X * G') := by
  have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : L) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have hl : f (secThL μ j X) = ∑ a, ∑ b, X a b • f (secTh μ j a b) := by
    simp only [secThL_apply, map_sum, map_smul]
  rw [hl]
  conv_rhs => rw [hX]
  simp only [h, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, map_sum,
    map_smul]

@[expose] def xkEnd (κ t : L) : Module.End L (RootModule TwistTag.D4.tag L) :=
  xOp TwistTag.D4.tag L 0 t * xOp TwistTag.D4.tag L 1 (κ * t) *
    xOp TwistTag.D4.tag L 3 (κ ^ 2 * t)

@[expose] def ykEnd (κ t : L) : Module.End L (RootModule TwistTag.D4.tag L) :=
  yOp TwistTag.D4.tag L 0 t * yOp TwistTag.D4.tag L 1 (κ ^ 2 * t) *
    yOp TwistTag.D4.tag L 3 (κ * t)

@[expose] def nE (i : Fin TwistTag.D4.tag.rank) : Module.End L (RootModule TwistTag.D4.tag L) :=
  (weylElt TwistTag.D4.tag L i 1 : Module.End L (RootModule TwistTag.D4.tag L))

set_option maxHeartbeats 4000000 in
theorem xk_secTh0 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    xkEnd (μ) t (secTh0 μ a b) = secThL μ 0 (Matrix.transvection 0 1 t *
      Matrix.single a b 1 * Matrix.transvection 0 1 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [xkEnd, secTh0, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      x0_0001, x0_000m, x0_0011, x0_00m0, x0_00mm, x0_0100, x0_0110, x0_0111, x0_0m00, x0_0mm0,
      x0_0mmm, x0_1000, x0_1010, x0_1011, x0_1110, x0_1111, x0_h0, x0_h1, x0_h2, x0_h3, x0_m000,
      x0_m0m0, x0_m0mm, x0_mmm0, x1_0001, x1_000m, x1_0011, x1_00m0, x1_00mm, x1_0100, x1_0110,
      x1_0111, x1_0m00, x1_0mm0, x1_0mmm, x1_1000, x1_1010, x1_1011, x1_1110, x1_1111, x1_h0,
      x1_h1, x1_h2, x1_h3, x1_m000, x1_m0m0, x1_m0mm, x1_mmm0, x3_0001, x3_000m, x3_0011, x3_00mm,
      x3_0100, x3_0110, x3_0111, x3_0m00, x3_0mm0, x3_0mmm, x3_1000, x3_1010, x3_1011, x3_1110,
      x3_h0, x3_h1, x3_h2, x3_h3, x3_m000, x3_m0m0, x3_m0mm, x3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

set_option maxHeartbeats 4000000 in
theorem xk_secTh1 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    xkEnd (μ ^ 2) t (secTh1 μ a b) = secThL μ 1 (Matrix.transvection 1 2 t *
      Matrix.single a b 1 * Matrix.transvection 1 2 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [xkEnd, secTh1, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      x0_0001, x0_000m, x0_0011, x0_00m0, x0_00mm, x0_0100, x0_0110, x0_0111, x0_0m00, x0_0mm0,
      x0_0mmm, x0_1000, x0_1010, x0_1011, x0_1110, x0_1111, x0_h0, x0_h1, x0_h2, x0_h3, x0_m000,
      x0_m0m0, x0_m0mm, x0_mmm0, x1_0001, x1_000m, x1_0011, x1_00m0, x1_00mm, x1_0100, x1_0110,
      x1_0111, x1_0m00, x1_0mm0, x1_0mmm, x1_1000, x1_1010, x1_1011, x1_1110, x1_1111, x1_h0,
      x1_h1, x1_h2, x1_h3, x1_m000, x1_m0m0, x1_m0mm, x1_mmm0, x3_0001, x3_000m, x3_0011, x3_00mm,
      x3_0100, x3_0110, x3_0111, x3_0m00, x3_0mm0, x3_0mmm, x3_1000, x3_1010, x3_1011, x3_1110,
      x3_h0, x3_h1, x3_h2, x3_h3, x3_m000, x3_m0m0, x3_m0mm, x3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

set_option maxHeartbeats 4000000 in
theorem xk_secTh2 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    xkEnd (1) t (secTh2 μ a b) = secThL μ 2 (Matrix.transvection 0 2 t *
      Matrix.single a b 1 * Matrix.transvection 0 2 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [xkEnd, secTh2, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      x0_0001, x0_000m, x0_0011, x0_00m0, x0_00mm, x0_0100, x0_0110, x0_0111, x0_0m00, x0_0mm0,
      x0_0mmm, x0_1000, x0_1010, x0_1011, x0_1110, x0_1111, x0_h0, x0_h1, x0_h2, x0_h3, x0_m000,
      x0_m0m0, x0_m0mm, x0_mmm0, x1_0001, x1_000m, x1_0011, x1_00m0, x1_00mm, x1_0100, x1_0110,
      x1_0111, x1_0m00, x1_0mm0, x1_0mmm, x1_1000, x1_1010, x1_1011, x1_1110, x1_1111, x1_h0,
      x1_h1, x1_h2, x1_h3, x1_m000, x1_m0m0, x1_m0mm, x1_mmm0, x3_0001, x3_000m, x3_0011, x3_00mm,
      x3_0100, x3_0110, x3_0111, x3_0m00, x3_0mm0, x3_0mmm, x3_1000, x3_1010, x3_1011, x3_1110,
      x3_h0, x3_h1, x3_h2, x3_h3, x3_m000, x3_m0m0, x3_m0mm, x3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

set_option maxHeartbeats 4000000 in
theorem yk_secTh0 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    ykEnd (μ) t (secTh0 μ a b) = secThL μ 0 (Matrix.transvection 1 0 t *
      Matrix.single a b 1 * Matrix.transvection 1 0 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [ykEnd, secTh0, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      y0_0001, y0_000m, y0_0010, y0_0011, y0_00mm, y0_0100, y0_0110, y0_0111, y0_0m00, y0_0mm0,
      y0_0mmm, y0_1000, y0_1010, y0_1011, y0_1110, y0_h0, y0_h1, y0_h2, y0_h3, y0_m000, y0_m0m0,
      y0_m0mm, y0_mmm0, y0_mmmm, y1_0001, y1_000m, y1_0010, y1_0011, y1_00mm, y1_0100, y1_0110,
      y1_0111, y1_0m00, y1_0mm0, y1_0mmm, y1_1000, y1_1010, y1_1011, y1_1110, y1_h0, y1_h1, y1_h2,
      y1_h3, y1_m000, y1_m0m0, y1_m0mm, y1_mmm0, y1_mmmm, y3_0001, y3_000m, y3_0011, y3_00mm,
      y3_0100, y3_0110, y3_0111, y3_0m00, y3_0mm0, y3_0mmm, y3_1000, y3_1010, y3_1011, y3_1110,
      y3_h0, y3_h1, y3_h2, y3_h3, y3_m000, y3_m0m0, y3_m0mm, y3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

set_option maxHeartbeats 4000000 in
theorem yk_secTh1 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    ykEnd (μ ^ 2) t (secTh1 μ a b) = secThL μ 1 (Matrix.transvection 2 1 t *
      Matrix.single a b 1 * Matrix.transvection 2 1 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [ykEnd, secTh1, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      y0_0001, y0_000m, y0_0010, y0_0011, y0_00mm, y0_0100, y0_0110, y0_0111, y0_0m00, y0_0mm0,
      y0_0mmm, y0_1000, y0_1010, y0_1011, y0_1110, y0_h0, y0_h1, y0_h2, y0_h3, y0_m000, y0_m0m0,
      y0_m0mm, y0_mmm0, y0_mmmm, y1_0001, y1_000m, y1_0010, y1_0011, y1_00mm, y1_0100, y1_0110,
      y1_0111, y1_0m00, y1_0mm0, y1_0mmm, y1_1000, y1_1010, y1_1011, y1_1110, y1_h0, y1_h1, y1_h2,
      y1_h3, y1_m000, y1_m0m0, y1_m0mm, y1_mmm0, y1_mmmm, y3_0001, y3_000m, y3_0011, y3_00mm,
      y3_0100, y3_0110, y3_0111, y3_0m00, y3_0mm0, y3_0mmm, y3_1000, y3_1010, y3_1011, y3_1110,
      y3_h0, y3_h1, y3_h2, y3_h3, y3_m000, y3_m0m0, y3_m0mm, y3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

set_option maxHeartbeats 4000000 in
theorem yk_secTh2 [CharP L 2] (μ : L) (hμ : μ ^ 2 + μ + 1 = 0) (t : L) (a b : Fin 3) :
    ykEnd (1) t (secTh2 μ a b) = secThL μ 2 (Matrix.transvection 2 0 t *
      Matrix.single a b 1 * Matrix.transvection 2 0 (-t)) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  fin_cases a <;> fin_cases b <;>
  · simp only [ykEnd, secTh2, Module.End.mul_apply, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      y0_0001, y0_000m, y0_0010, y0_0011, y0_00mm, y0_0100, y0_0110, y0_0111, y0_0m00, y0_0mm0,
      y0_0mmm, y0_1000, y0_1010, y0_1011, y0_1110, y0_h0, y0_h1, y0_h2, y0_h3, y0_m000, y0_m0m0,
      y0_m0mm, y0_mmm0, y0_mmmm, y1_0001, y1_000m, y1_0010, y1_0011, y1_00mm, y1_0100, y1_0110,
      y1_0111, y1_0m00, y1_0mm0, y1_0mmm, y1_1000, y1_1010, y1_1011, y1_1110, y1_h0, y1_h1, y1_h2,
      y1_h3, y1_m000, y1_m0m0, y1_m0mm, y1_mmm0, y1_mmmm, y3_0001, y3_000m, y3_0011, y3_00mm,
      y3_0100, y3_0110, y3_0111, y3_0m00, y3_0mm0, y3_0mmm, y3_1000, y3_1010, y3_1011, y3_1110,
      y3_h0, y3_h1, y3_h2, y3_h3, y3_m000, y3_m0m0, y3_m0mm, y3_mmm0]
    simp only [secThL_apply, secTh, secTh0, secTh1, secTh2, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> grind)

theorem nE_secTh1 [CharP L 2] (μ : L) (a b : Fin 3) :
    nE 2 (secTh1 μ a b) = secTh0 μ a b := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [← one_smul L (secTh0 μ a b)]
  fin_cases a <;> fin_cases b <;>
  · simp only [nE, secTh1, secTh0, smul_add, Module.End.mul_apply, map_add, map_smul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      n2_0001, n2_000m, n2_0011, n2_00mm, n2_0100, n2_0110, n2_0111, n2_0m00, n2_0mm0, n2_0mmm,
      n2_1000, n2_1010, n2_1011, n2_1110, n2_h0, n2_h1, n2_h2, n2_h3, n2_m000, n2_m0m0, n2_m0mm,
      n2_mmm0]
    all_goals (match_scalars <;> grind)

theorem nE_secTh2 [CharP L 2] (μ : L) (a b : Fin 3) :
    nE 0 (nE 1 (nE 3 (nE 2 (secTh2 μ a b)))) = secTh0 μ a b := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [← one_smul L (secTh0 μ a b)]
  fin_cases a <;> fin_cases b <;>
  · simp only [nE, secTh2, secTh0, smul_add, Module.End.mul_apply, map_add, map_smul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      n0_0001, n0_000m, n0_0010, n0_0011, n0_00m0, n0_00mm, n0_0100, n0_0110, n0_0m00, n0_0mm0,
      n0_1000, n0_1011, n0_1110, n0_1111, n0_h0, n0_h1, n0_h2, n0_h3, n0_m000, n0_m0mm, n0_mmm0,
      n0_mmmm, n1_0001, n1_000m, n1_0010, n1_00m0, n1_0100, n1_0110, n1_0111, n1_0m00, n1_0mm0,
      n1_0mmm, n1_1000, n1_1010, n1_1011, n1_1111, n1_h0, n1_h1, n1_h2, n1_h3, n1_m000, n1_m0m0,
      n1_m0mm, n1_mmmm, n2_0001, n2_000m, n2_0011, n2_00mm, n2_0100, n2_0110, n2_0111, n2_0m00,
      n2_0mm0, n2_0mmm, n2_1000, n2_1010, n2_1011, n2_1110, n2_h0, n2_h1, n2_h2, n2_h3, n2_m000,
      n2_m0m0, n2_m0mm, n2_mmm0, n3_0001, n3_000m, n3_0011, n3_00mm, n3_0100, n3_0110, n3_0111,
      n3_0m00, n3_0mm0, n3_0mmm, n3_1000, n3_1010, n3_1011, n3_1110, n3_h0, n3_h1, n3_h2, n3_h3,
      n3_m000, n3_m0m0, n3_m0mm, n3_mmm0]
    all_goals (match_scalars <;> grind)

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
