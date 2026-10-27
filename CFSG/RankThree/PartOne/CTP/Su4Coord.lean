module

public import CFSG.RankThree.PartOne.CTP.Su4Std
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K}

@[expose] def wittMat (b : Fin 4 → (Fin 4 → K)) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun r i => b i r

theorem wittMat_mulVec_single (b : Fin 4 → (Fin 4 → K)) (i : Fin 4) :
    wittMat b *ᵥ Pi.single i 1 = b i := by
  ext r
  simp [wittMat]

theorem conjTr_wittMat_mul (b : Fin 4 → (Fin 4 → K))
    (hb : ∀ i j, herm σ (b i) (b j) = if j = Fin.rev i then 1 else 0) :
    conjTr σ (wittMat b) * wittMat b = antidiag 4 := by
  ext i j
  have h := hb i j
  rw [herm_def] at h
  rw [Matrix.mul_apply]
  simpa [conjTr, wittMat, antidiag] using h

theorem antidiag_mul_self : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * antidiag 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, Matrix.mul_apply, Fin.sum_univ_four, Fin.rev]

theorem exists_wittConj (b : Fin 4 → (Fin 4 → K))
    (hb : ∀ i j, herm σ (b i) (b j) = if j = Fin.rev i then 1 else 0) :
    ∃ Q : GL (Fin 4) K, conjTr σ (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) =
        antidiag 4 ∧
      ∀ i, (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single i 1 = b i := by
  have hW := conjTr_wittMat_mul (σ := σ) b hb
  have hdet : (wittMat b).det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := antidiag 4 * conjTr σ (wittMat b)) ?_
    rw [Matrix.mul_assoc, hW, antidiag_mul_self]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (wittMat b) hdet, hW, wittMat_mulVec_single b⟩

section Conj

variable {Q : GL (Fin 4) K}
  (hQ : conjTr σ (Q : Matrix (Fin 4) (Fin 4) K) * (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4)

theorem mulVec_injective_of_unit (Q : GL (Fin 4) K) :
    Function.Injective ((Q : Matrix (Fin 4) (Fin 4) K).mulVec) := by
  intro x y h
  have h1 := congrArg (fun v => ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ v) h
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  exact h1

include hQ in
theorem smul_conjEquiv (s : SU σ 4) (x : Fin 4 → K) :
    (conjEquiv Q hQ s : SUid σ 4) • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ x) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ (matS σ s *ᵥ x) := by
  rw [smul_def, coe_conjEquiv]
  have hQQ : ((Q⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      (Q : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, hQQ, Matrix.mul_one, ← Matrix.mulVec_mulVec]

include hQ in
theorem le_map_lbEmb_of_fix {A : Subgroup (SUid σ 4)}
    (h0 : ∀ a ∈ A, a • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 0 1) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 0 1)
    (h3 : ∀ a ∈ A, a • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 3 1) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 3 1) :
    A ≤ (lbEmb σ).range.map (conjEquiv Q hQ).toMonoidHom := by
  intro a ha
  have has : conjEquiv Q hQ ((conjEquiv Q hQ).symm a) = a := (conjEquiv Q hQ).apply_symm_apply a
  refine ⟨(conjEquiv Q hQ).symm a, mem_range_lbEmb_of_fix _ ?_ ?_, has⟩
  · rw [mem_stabVec]
    apply mulVec_injective_of_unit Q
    rw [← smul_conjEquiv hQ, has]
    exact h0 a ha
  · rw [mem_stabVec]
    apply mulVec_injective_of_unit Q
    rw [← smul_conjEquiv hQ, has]
    exact h3 a ha

include hQ in
theorem eq_map_lbEmb_of_fix [Finite K] {A : Subgroup (SUid σ 4)}
    (hcard : Nat.card A = Nat.card (SU σ 2))
    (h0 : ∀ a ∈ A, a • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 0 1) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 0 1)
    (h3 : ∀ a ∈ A, a • ((Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 3 1) =
      (Q : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single 3 1) :
    A = (lbEmb σ).range.map (conjEquiv Q hQ).toMonoidHom := by
  refine Subgroup.eq_of_le_of_card_ge (le_map_lbEmb_of_fix hQ h0 h3) ?_
  rw [Subgroup.card_map_of_injective (conjEquiv Q hQ).injective, natCard_range_lbEmb, hcard]

end Conj

end CFSG.RankThree.PartOne.CTP
