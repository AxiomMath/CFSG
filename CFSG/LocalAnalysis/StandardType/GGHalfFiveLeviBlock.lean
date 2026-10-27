module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem resMat_apply_fin' {n : ℕ} (A : Matrix (Fin n) (Fin n) F4) (r s : Fin (n * 2)) :
    resMat n A r s =
      f4Eps (A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm s).1)
        (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm s).2 := by
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply r, ← finProdFinEquiv.apply_symm_apply s]
  exact resMat_apply n A _ _ _ _

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

private theorem slLowerBlockMat_apply_eq' {n : ℕ} {F : Type} [Field F]
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

private theorem slUpperBlockMat_apply_eq' {n : ℕ} {F : Type} [Field F]
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

private theorem resMat_slLowerBlockMat_three (A : Matrix (Fin 2) (Fin 2) F4) :
    slLowerBlockMat 5 F2 (slLowerBlockMat 4 F2 (resMat 2 A)) =
      resMat 3 (slLowerBlockMat 2 F4 A) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [slLowerBlockMat_apply_eq', resMat_apply_fin' (n := 2), resMat_apply_fin' (n := 3),
      finProdFinEquiv_symm_apply (m := 2) (n := 2), finProdFinEquiv_symm_apply (m := 3) (n := 2),
      Fin.divNat, Fin.modNat]

private theorem resMat_slUpperBlockMat_three (A : Matrix (Fin 2) (Fin 2) F4) :
    slUpperBlockMat 5 F2 (slUpperBlockMat 4 F2 (resMat 2 A)) =
      resMat 3 (slUpperBlockMat 2 F4 A) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [slUpperBlockMat_apply_eq', resMat_apply_fin' (n := 2), resMat_apply_fin' (n := 3),
      finProdFinEquiv_symm_apply (m := 2) (n := 2), finProdFinEquiv_symm_apply (m := 3) (n := 2),
      Fin.divNat, Fin.modNat,
      castPred6_0, castPred6_1, castPred6_2, castPred6_3, castPred6_4,
      castPred5_0, castPred5_1, castPred5_2, castPred5_3]

private theorem slLower2Hom_resSL (S : SpecialLinearGroup (Fin 2) F4) :
    slLower2Hom 3 (resSL 2 S) = resSL 3 (slLowerBlockHom 2 F4 S) := by
  apply Subtype.ext
  change slLowerBlockMat 5 F2 (slLowerBlockMat 4 F2 (resMat 2 (S : Matrix (Fin 2) (Fin 2) F4))) =
    resMat 3 (slLowerBlockMat 2 F4 (S : Matrix (Fin 2) (Fin 2) F4))
  exact resMat_slLowerBlockMat_three (S : Matrix (Fin 2) (Fin 2) F4)

private theorem slUpper2Hom_resSL (S : SpecialLinearGroup (Fin 2) F4) :
    slUpper2Hom 3 (resSL 2 S) = resSL 3 (slUpperBlockHom 2 F4 S) := by
  apply Subtype.ext
  change slUpperBlockMat 5 F2 (slUpperBlockMat 4 F2 (resMat 2 (S : Matrix (Fin 2) (Fin 2) F4))) =
    resMat 3 (slUpperBlockMat 2 F4 (S : Matrix (Fin 2) (Fin 2) F4))
  exact resMat_slUpperBlockMat_three (S : Matrix (Fin 2) (Fin 2) F4)

private noncomputable def f4OrderThree : SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![1, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩

private theorem f4OrderThree_pow_three : f4OrderThree ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    show ((f4OrderThree : SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) =
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F4) from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ, CharTwo.add_self_eq_zero]

private theorem f4OrderThree_ne_one : f4OrderThree ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  rw [Matrix.SpecialLinearGroup.coe_one,
    show ((f4OrderThree : SpecialLinearGroup (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4) =
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F4) from rfl] at h01
  simp at h01

private theorem four_le_natCard_F4 : 4 ≤ Nat.card F4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem exists_levi_perfect :
    ∃ P : Subgroup (SpecialLinearGroup (Fin (3 + 1)) F2), ⁅P, P⁆ = P ∧
      (∃ g ∈ P, g ≠ 1 ∧ g ^ 3 = 1) ∧
      P.map (slLower2Hom 3) ≤ sl3four ∧ P.map (slUpper2Hom 3) ≤ sl3four := by
  refine ⟨(resSL 2).range, ?_, ?_, ?_, ?_⟩
  · haveI : Group.IsPerfect (SpecialLinearGroup (Fin 2) F4) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F4 four_le_natCard_F4
    haveI : Group.IsPerfect ↥(resSL 2).range := Group.IsPerfect.range (resSL 2)
    exact Subgroup.commutator_eq_self
  · refine ⟨resSL 2 f4OrderThree, MonoidHom.mem_range.mpr ⟨f4OrderThree, rfl⟩, ?_, ?_⟩
    · intro h
      exact f4OrderThree_ne_one (resSL_injective 2 (by rw [h, map_one]))
    · rw [← map_pow, f4OrderThree_pow_three, map_one]
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨S, rfl⟩ := MonoidHom.mem_range.mp hp
    rw [slLower2Hom_resSL]
    exact MonoidHom.mem_range.mpr ⟨slLowerBlockHom 2 F4 S, rfl⟩
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨S, rfl⟩ := MonoidHom.mem_range.mp hp
    rw [slUpper2Hom_resSL]
    exact MonoidHom.mem_range.mpr ⟨slUpperBlockHom 2 F4 S, rfl⟩

end CFSG.StandardType.GGHalf

end
