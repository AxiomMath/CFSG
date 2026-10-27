module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem f4Omega_sq' : f4Omega ^ 2 = f4Omega + 1 := by
  have h : f4Omega ^ 2 + (f4Omega + 1) = 0 := by
    rw [← add_assoc]; exact f4Omega_sq
  have h2 := (add_eq_zero_iff_eq_neg).mp h
  rwa [CharTwo.neg_eq] at h2

theorem det_low5 : (!![1, 0, 0; 0, 0, 1; 0, 1, f4Omega] : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [CharTwo.neg_eq]

theorem det_up5 : (!![0, 1, 0; 1, f4Omega, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [CharTwo.neg_eq]

@[expose] noncomputable def low5 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, f4Omega], det_low5⟩

@[expose] noncomputable def up5 : SpecialLinearGroup (Fin 3) F4 :=
  ⟨!![0, 1, 0; 1, f4Omega, 0; 0, 0, 1], det_up5⟩

theorem trace_low5 : Matrix.trace (low5 : Matrix (Fin 3) (Fin 3) F4) = f4Omega ^ 2 := by
  change Matrix.trace (!![1, 0, 0; 0, 0, 1; 0, 1, f4Omega] : Matrix (Fin 3) (Fin 3) F4) =
    f4Omega ^ 2
  rw [Matrix.trace_fin_three]
  simp [CharTwo.neg_eq]
  rw [f4Omega_sq']
  try ring

theorem trace_up5 : Matrix.trace (up5 : Matrix (Fin 3) (Fin 3) F4) = f4Omega ^ 2 := by
  change Matrix.trace (!![0, 1, 0; 1, f4Omega, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F4) =
    f4Omega ^ 2
  rw [Matrix.trace_fin_three]
  simp [CharTwo.neg_eq]
  rw [f4Omega_sq']
  try ring

theorem trace_low5_inv :
    Matrix.trace ((low5⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      f4Omega ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change Matrix.trace
    (Matrix.adjugate (!![1, 0, 0; 0, 0, 1; 0, 1, f4Omega] : Matrix (Fin 3) (Fin 3) F4)) =
      f4Omega ^ 2
  rw [Matrix.adjugate_fin_three]
  rw [Matrix.trace_fin_three]
  simp [CharTwo.neg_eq]
  rw [f4Omega_sq']
  try ring

theorem trace_up5_inv :
    Matrix.trace ((up5⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      f4Omega ^ 2 := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  change Matrix.trace
    (Matrix.adjugate (!![0, 1, 0; 1, f4Omega, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F4)) =
      f4Omega ^ 2
  rw [Matrix.adjugate_fin_three]
  rw [Matrix.trace_fin_three]
  simp [CharTwo.neg_eq]
  rw [f4Omega_sq']
  try ring

private theorem slLowerBlockMat_zero_zero {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) : slLowerBlockMat n F A 0 0 = 1 := by
  rw [← slLowerBlockEquiv_inl (n := n) (0 : Fin 1)]
  rw [slLowerBlockMat_apply, Matrix.fromBlocks_apply₁₁]
  simp

private theorem slLowerBlockMat_zero_succ {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (j : Fin n) : slLowerBlockMat n F A 0 j.succ = 0 := by
  rw [← slLowerBlockEquiv_inl (n := n) (0 : Fin 1),
    ← slLowerBlockEquiv_inr (n := n) j]
  rw [slLowerBlockMat_apply, Matrix.fromBlocks_apply₁₂]
  simp

private theorem slLowerBlockMat_succ_zero {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (i : Fin n) : slLowerBlockMat n F A i.succ 0 = 0 := by
  rw [← slLowerBlockEquiv_inr (n := n) i,
    ← slLowerBlockEquiv_inl (n := n) (0 : Fin 1)]
  rw [slLowerBlockMat_apply, Matrix.fromBlocks_apply₂₁]
  simp

private theorem slLowerBlockMat_succ_succ {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    slLowerBlockMat n F A i.succ j.succ = A i j := by
  rw [← slLowerBlockEquiv_inr (n := n) i, ← slLowerBlockEquiv_inr (n := n) j]
  rw [slLowerBlockMat_apply, Matrix.fromBlocks_apply₂₂]

private theorem slLowerBlockMat_apply_eq {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (r s : Fin (n + 1)) :
    slLowerBlockMat n F A r s =
      if hr : r = 0 then (if s = 0 then 1 else 0)
      else if hs : s = 0 then 0
      else A (Fin.pred r hr) (Fin.pred s hs) := by
  induction r using Fin.cases with
  | zero =>
      induction s using Fin.cases with
      | zero => simp [slLowerBlockMat_zero_zero]
      | succ j => simp [slLowerBlockMat_zero_succ]
  | succ i =>
      induction s using Fin.cases with
      | zero => simp [slLowerBlockMat_succ_zero]
      | succ j => simp [slLowerBlockMat_succ_succ]

private theorem slUpperBlockMat_apply_castSucc_castSucc {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    slUpperBlockMat n F A i.castSucc j.castSucc = A i j := by
  rw [show i.castSucc = finSumFinEquiv (Sum.inl i) from rfl,
    show j.castSucc = finSumFinEquiv (Sum.inl j) from rfl]
  rw [slUpperBlockMat_apply, Matrix.fromBlocks_apply₁₁]

private theorem slUpperBlockMat_apply_castSucc_last {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    slUpperBlockMat n F A i.castSucc (Fin.last n) = 0 := by
  rw [show i.castSucc = finSumFinEquiv (Sum.inl i) from rfl,
    show Fin.last n = finSumFinEquiv (Sum.inr 0) from rfl]
  rw [slUpperBlockMat_apply, Matrix.fromBlocks_apply₁₂]
  simp

private theorem slUpperBlockMat_apply_last_castSucc {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    slUpperBlockMat n F A (Fin.last n) j.castSucc = 0 := by
  rw [show Fin.last n = finSumFinEquiv (Sum.inr 0) from rfl,
    show j.castSucc = finSumFinEquiv (Sum.inl j) from rfl]
  rw [slUpperBlockMat_apply, Matrix.fromBlocks_apply₂₁]
  simp

private theorem slUpperBlockMat_apply_last_last {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) :
    slUpperBlockMat n F A (Fin.last n) (Fin.last n) = 1 := by
  rw [show Fin.last n = finSumFinEquiv (Sum.inr 0) from rfl]
  rw [slUpperBlockMat_apply, Matrix.fromBlocks_apply₂₂]
  simp

private theorem slUpperBlockMat_apply_eq {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n) (Fin n) F) (r s : Fin (n + 1)) :
    slUpperBlockMat n F A r s =
      if hr : r = Fin.last n then (if s = Fin.last n then 1 else 0)
      else if hs : s = Fin.last n then 0
      else A (Fin.castPred r hr) (Fin.castPred s hs) := by
  induction r using Fin.lastCases with
  | last =>
      induction s using Fin.lastCases with
      | last => simp [slUpperBlockMat_apply_last_last]
      | cast j => simp [slUpperBlockMat_apply_last_castSucc]
  | cast i =>
      induction s using Fin.lastCases with
      | last => simp [slUpperBlockMat_apply_castSucc_last]
      | cast j => simp [slUpperBlockMat_apply_castSucc_castSucc]

private theorem resMat_apply_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (r s : Fin (n * 2)) :
    resMat n A r s =
      f4Eps (A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm s).1)
        (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm s).2 := by
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply r, ← finProdFinEquiv.apply_symm_apply s]
  exact resMat_apply n A _ _ _ _

private theorem castPred6_0 (h : (0 : Fin 6) ≠ Fin.last 5) :
    Fin.castPred (0 : Fin 6) h = (0 : Fin 5) := by rw [Fin.castPred_mk]; rfl

private theorem castPred6_1 (h : (1 : Fin 6) ≠ Fin.last 5) :
    Fin.castPred (1 : Fin 6) h = (1 : Fin 5) := by rw [Fin.castPred_mk]; rfl

private theorem castPred6_2 (h : (2 : Fin 6) ≠ Fin.last 5) :
    Fin.castPred (2 : Fin 6) h = (2 : Fin 5) := by rw [Fin.castPred_mk]; rfl

private theorem castPred6_3 (h : (3 : Fin 6) ≠ Fin.last 5) :
    Fin.castPred (3 : Fin 6) h = (3 : Fin 5) := by rw [Fin.castPred_mk]; rfl

private theorem castPred6_4 (h : (4 : Fin 6) ≠ Fin.last 5) :
    Fin.castPred (4 : Fin 6) h = (4 : Fin 5) := by rw [Fin.castPred_mk]; rfl

private theorem castPred5_0 (h : (0 : Fin 5) ≠ Fin.last 4) :
    Fin.castPred (0 : Fin 5) h = (0 : Fin 4) := by rw [Fin.castPred_mk]; rfl

private theorem castPred5_1 (h : (1 : Fin 5) ≠ Fin.last 4) :
    Fin.castPred (1 : Fin 5) h = (1 : Fin 4) := by rw [Fin.castPred_mk]; rfl

private theorem castPred5_2 (h : (2 : Fin 5) ≠ Fin.last 4) :
    Fin.castPred (2 : Fin 5) h = (2 : Fin 4) := by rw [Fin.castPred_mk]; rfl

private theorem castPred5_3 (h : (3 : Fin 5) ≠ Fin.last 4) :
    Fin.castPred (3 : Fin 5) h = (3 : Fin 4) := by rw [Fin.castPred_mk]; rfl

private noncomputable def S5t : SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![0, 1; 1, f4Omega], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩

private noncomputable def J4 : Matrix (Fin 4) (Fin 4) F2 :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 1]

private theorem resMat2_S5t : resMat 2 (↑S5t) = J4 := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [J4, S5t, f4Eps_omega, resMat_apply_fin (n := 2),
      finProdFinEquiv_symm_apply (m := 2) (n := 2), Fin.divNat, Fin.modNat]

theorem levi_agree_s5 :
    ∃ j : SpecialLinearGroup (Fin (3 + 1)) F2,
      slLower2Hom 3 j = resSL 3 low5 ∧ slUpper2Hom 3 j = resSL 3 up5 := by
  refine ⟨resSL 2 S5t, ?_, ?_⟩
  · apply Subtype.ext
    change slLowerBlockMat 5 F2 (slLowerBlockMat 4 F2 (resMat 2 (↑S5t))) = resMat 3 (↑low5)
    rw [resMat2_S5t]
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [slLowerBlockMat_apply_eq, J4, low5, f4Eps_omega, resMat_apply_fin (n := 3),
        finProdFinEquiv_symm_apply (m := 3) (n := 2), Fin.divNat, Fin.modNat]
  · apply Subtype.ext
    change slUpperBlockMat 5 F2 (slUpperBlockMat 4 F2 (resMat 2 (↑S5t))) = resMat 3 (↑up5)
    rw [resMat2_S5t]
    ext r s
    fin_cases r <;> fin_cases s <;>
      simp [slUpperBlockMat_apply_eq, J4, up5, f4Eps_omega, resMat_apply_fin (n := 3),
        finProdFinEquiv_symm_apply (m := 3) (n := 2), Fin.divNat, Fin.modNat,
        castPred6_0, castPred6_1, castPred6_2, castPred6_3, castPred6_4,
        castPred5_0, castPred5_1, castPred5_2, castPred5_3]

end CFSG.StandardType.GGHalf

end
