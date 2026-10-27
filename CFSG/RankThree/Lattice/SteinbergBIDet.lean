module

public import CFSG.RankThree.Lattice.SteinbergBIPoly

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley Matrix Polynomial

variable {n : ℕ}

@[expose] def lcolAdd (n : ℕ) (M : List (List ℤ)) (op : ℕ × ℕ × ℤ) : List (List ℤ) :=
  lofFn n fun r s => if (s : ℕ) = op.2.1 then lget M r s + op.2.2 * lget M r op.1 else lget M r s

@[expose] def lcolAdds (n : ℕ) (M : List (List ℤ)) (ops : List (ℕ × ℕ × ℤ)) : List (List ℤ) :=
  ops.foldl (lcolAdd n) M

@[expose] def opsValid (n : ℕ) (ops : List (ℕ × ℕ × ℤ)) : Bool :=
  ops.all fun op => decide (op.1 < n) && decide (op.2.1 < n) && decide (op.1 ≠ op.2.1)

theorem toMat_lcolAdd (M : List (List ℤ)) {i j : Fin n} (c : ℤ) :
    toMat n (lcolAdd n M (i, j, c)) = toMat n M * transvection i j c := by
  ext r s
  rw [lcolAdd, toMat_lofFn, Matrix.of_apply]
  by_cases hs : s = j
  · subst hs
    simp only [↓reduceIte, mul_transvection_apply_same]
    rfl
  · rw [ite_eq_right (fun h => hs (Fin.ext h)), mul_transvection_apply_of_ne i j r s hs]
    rfl

theorem det_toMat_lcolAdds (M : List (List ℤ)) (ops : List (ℕ × ℕ × ℤ))
    (h : opsValid n ops = true) : (toMat n (lcolAdds n M ops)).det = (toMat n M).det := by
  induction ops generalizing M with
  | nil => rfl
  | cons op ops ih =>
    simp only [opsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi, hj⟩, hij⟩, h⟩ := h
    rw [lcolAdds, List.foldl_cons, ← lcolAdds, ih _ (by simpa [opsValid] using h)]
    obtain ⟨i, j, c⟩ := op
    have e : lcolAdd n M (i, j, c) = lcolAdd n M ((⟨i, hi⟩ : Fin n), (⟨j, hj⟩ : Fin n), c) := rfl
    rw [e, toMat_lcolAdd, Matrix.det_mul, det_transvection_of_ne _ _ (fun h' => hij
      (congrArg Fin.val h')), mul_one]

theorem det_toMat_eq_of_colAdds (M : List (List ℤ)) (ops : List (ℕ × ℕ × ℤ))
    (hv : opsValid n ops = true) (ht : lowerTri n (lcolAdds n M ops) = true) :
    (toMat n M).det = ldiagProd n (lcolAdds n M ops) := by
  rw [← det_toMat_lcolAdds M ops hv, det_toMat_of_lowerTri ht]

theorem charpoly_eq_of_conj {B B' w : Matrix (Fin n) (Fin n) ℤ} (h : B * B' = 1) :
    w.charpoly = (B' * w * B).charpoly := by
  have h' : B' * B = 1 := mul_eq_one_comm.1 h
  calc w.charpoly = (B * (B' * w)).charpoly := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    _ = (B' * w * B).charpoly := Matrix.charpoly_mul_comm _ _

@[expose] def ltopLeft (k : ℕ) (M : List (List ℤ)) : List (List ℤ) :=
  lofFn k fun i j => lget M i j

@[expose] def lbotRight (k m : ℕ) (M : List (List ℤ)) : List (List ℤ) :=
  lofFn m fun i j => lget M (k + i) (k + j)

@[expose] def lowerLeftZero (k m : ℕ) (M : List (List ℤ)) : Bool :=
  (List.finRange m).all fun i => (List.finRange k).all fun j => lget M (k + i) j == 0

theorem charpoly_eq_mul_of_blocks {k m : ℕ} (M : List (List ℤ))
    (h : lowerLeftZero k m M = true) :
    (toMat (k + m) M).charpoly = (toMat k (ltopLeft k M)).charpoly *
      (toMat m (lbotRight k m M)).charpoly := by
  rw [← Matrix.charpoly_reindex finSumFinEquiv.symm, ← fromBlocks_toBlocks
    (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (toMat (k + m) M))]
  have h21 : (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (toMat (k + m) M)).toBlocks₂₁ = 0 := by
    ext i j
    simp only [lowerLeftZero, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
    simp only [toBlocks₂₁, Matrix.reindex_apply, Matrix.of_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, toMat,
      Fin.val_natAdd, Fin.val_castAdd, Matrix.zero_apply]
    exact h i j
  rw [h21, charpoly_fromBlocks_zero₂₁]
  congr 2
  · ext i j
    simp [toBlocks₁₁, toMat, ltopLeft, lget_lofFn]
  · ext i j
    simp [toBlocks₂₂, toMat, lbotRight, lget_lofFn]

@[expose] def rootReflMat (τ : Tag) (r : Fin τ.rank → ℤ) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  1 - Matrix.vecMulVec r (Matrix.vecMul r τ.cartan)

@[expose] def gramMat (τ : Tag) {k : ℕ} (γ : Fin k → Fin τ.rank → ℤ) : Matrix (Fin k) (Fin k) ℤ :=
  Matrix.of fun i j => γ i ⬝ᵥ (τ.cartan *ᵥ γ j)

@[expose] def lrootRefl (n : ℕ) (C : List (List ℤ)) (r : List ℤ) : List (List ℤ) :=
  lofFn n fun a b =>
    (if a = b then 1 else 0) - vget r a * (List.ofFn fun k : Fin n => vget r k * lget C k b).sum

theorem toMat_lrootRefl (τ : Tag) {C : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan)
    (r : List ℤ) : toMat τ.rank (lrootRefl τ.rank C r) = rootReflMat τ (toVec τ.rank r) := by
  rw [lrootRefl, toMat_lofFn, rootReflMat, ← hC]
  ext a b
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    Matrix.vecMul, dotProduct, List.sum_ofFn]
  rfl

@[expose] def lgram (n k : ℕ) (C : List (List ℤ)) (γs : List (List ℤ)) : List (List ℤ) :=
  lofFn k fun i j => (List.ofFn fun a : Fin n => vget (γs.getD i []) a *
    (List.ofFn fun b : Fin n => lget C a b * vget (γs.getD j []) b).sum).sum

theorem toMat_lgram (τ : Tag) {C : List (List ℤ)} (hC : toMat τ.rank C = τ.cartan) (k : ℕ)
    (γs : List (List ℤ)) :
    toMat k (lgram τ.rank k C γs) =
      gramMat τ (fun i : Fin k => toVec τ.rank (γs.getD i [])) := by
  rw [lgram, toMat_lofFn, gramMat, ← hC]
  ext i j
  simp only [Matrix.of_apply, dotProduct, Matrix.mulVec, List.sum_ofFn]
  rfl

end CFSG.RankThree.Lattice
