module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBlock
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.FFModules.Natural

public section

namespace CFSG.Quasithin.H13.L3318

open Matrix

variable {K : Type} [Field K]

@[expose] def IsQ1 (X : Matrix (Fin 4) (Fin 4) K) : Prop :=
  X 0 0 = 1 ∧ ∀ i : Fin 3, X i.succ 0 = 0

@[expose] def IsRad1 (X : Matrix (Fin 4) (Fin 4) K) : Prop :=
  IsQ1 X ∧ ∀ i j : Fin 3, X i.succ j.succ = if i = j then 1 else 0

@[expose] def rowOf (X : Matrix (Fin 4) (Fin 4) K) : Fin 3 → K := fun j => X 0 j.succ

@[expose] def blk (X : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => X i.succ j.succ

omit [Field K] in
theorem blk_apply (X : Matrix (Fin 4) (Fin 4) K) (i j : Fin 3) : blk X i j = X i.succ j.succ :=
  rfl

omit [Field K] in
theorem blkAt_eq_blk (h : 1 + 3 ≤ 4) (X : Matrix (Fin 4) (Fin 4) K) :
    CFSG.QuasithinUnique.Vol2Native.A312L.blkAt 1 3 h X = blk X := by
  ext i j
  rw [CFSG.QuasithinUnique.Vol2Native.A312L.blkAt_apply, blk_apply]
  congr 1 <;> exact Fin.ext (by simp [Fin.succ]; omega)

theorem rowOf_mul {R R' : Matrix (Fin 4) (Fin 4) K} (hR : IsRad1 R) (hR' : IsRad1 R') :
    rowOf (R * R') = rowOf R + rowOf R' := by
  funext j
  simp only [rowOf, Pi.add_apply]
  rw [Matrix.mul_apply, Fin.sum_univ_succ, hR.1.1, one_mul]
  simp only [hR'.2]
  rw [Finset.sum_eq_single j (fun t _ htj => by rw [ite_eq_right htj, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, mul_one, add_comm]

theorem vecMul_rowOf {X R R' : Matrix (Fin 4) (Fin 4) K} (hX : IsQ1 X) (hR : IsRad1 R)
    (hR' : IsRad1 R') (h : R' * X = X * R) : Matrix.vecMul (rowOf R') (blk X) = rowOf R := by
  funext j
  have hl : (R' * X) 0 j.succ = X 0 j.succ + ∑ t : Fin 3, R' 0 t.succ * X t.succ j.succ := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hR'.1.1, one_mul]
  have hr : (X * R) 0 j.succ = R 0 j.succ + X 0 j.succ := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ, hX.1, one_mul]
    simp only [hR.2]
    rw [Finset.sum_eq_single j (fun t _ htj => by rw [ite_eq_right htj, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, mul_one]
  have h1 := congrFun (congrFun h 0) j.succ
  rw [hl, hr] at h1
  simp only [Matrix.vecMul, dotProduct, rowOf, blk_apply]
  linear_combination h1

theorem eq_dualMat {F : Type} [Field F] {r r' : Fin 3 → F}
    {g : SpecialLinearGroup (Fin 3) F} (h : Matrix.vecMul r' (g : Matrix (Fin 3) (Fin 3) F) = r) :
    r' = CFSG.RankThree.FFModules.dualMat g *ᵥ r := by
  rw [CFSG.RankThree.FFModules.dualMat, Matrix.mulVec_transpose, ← h, Matrix.vecMul_vecMul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.vecMul_one]

theorem mulVec_cons (X : Matrix (Fin 4) (Fin 4) K) (a : Fin 3 → K) :
    X *ᵥ Fin.cons 0 a = Fin.cons (rowOf X ⬝ᵥ a) (blk X *ᵥ a) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_zero, mul_zero,
      zero_add]
    simp only [Fin.cons_succ, rowOf, dotProduct]
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, mul_zero, zero_add,
      Fin.cons_succ]
    simp only [Fin.cons_succ, Matrix.mulVec, dotProduct, blk_apply]

theorem mulVec_cons_zero {X : Matrix (Fin 4) (Fin 4) K} (hX : IsQ1 X) (c : K) :
    X *ᵥ (Fin.cons c 0 : Fin 4 → K) = Fin.cons c 0 := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, hX.1, one_mul]
    simp
  · rw [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, hX.2 i, zero_mul,
      zero_add, Fin.cons_succ]
    simp

omit [Field K] in
theorem cons_add_cons {M : Type} [AddZeroClass M] (c c' : M) (a a' : Fin 3 → M) :
    (Fin.cons c a : Fin 4 → M) + Fin.cons c' a' = Fin.cons (c + c') (a + a') := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem eq_one_of_rowOf {R : Matrix (Fin 4) (Fin 4) K} (hR : IsRad1 R) (h0 : rowOf R = 0) :
    R = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
  · rw [hR.1.1, Matrix.one_apply_eq]
  · have := congrFun h0 j
    simp only [rowOf, Pi.zero_apply] at this
    rw [this, Matrix.one_apply_ne (Fin.succ_ne_zero j).symm]
  · rw [hR.1.2 i, Matrix.one_apply_ne (Fin.succ_ne_zero i)]
  · rw [hR.2 i j, Matrix.one_apply]
    simp [Fin.succ_inj]

end CFSG.Quasithin.H13.L3318
