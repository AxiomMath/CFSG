module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix
open scoped MatrixGroups

section Conj

variable {K : Type} [Field K]

theorem glInv_mul (P : GL (Fin 2) K) :
    ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (P : Matrix (Fin 2) (Fin 2) K) = 1 :=
  Units.inv_mul P

theorem mul_glInv (P : GL (Fin 2) K) :
    (P : Matrix (Fin 2) (Fin 2) K) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
  Units.mul_inv P

theorem conj_mul_aux (Pm Pi X Y : Matrix (Fin 2) (Fin 2) K) (h : Pi * Pm = 1) :
    Pm * (X * Y) * Pi = (Pm * X * Pi) * (Pm * Y * Pi) := by
  symm
  calc (Pm * X * Pi) * (Pm * Y * Pi) = Pm * X * (Pi * Pm) * Y * Pi := by
        simp only [Matrix.mul_assoc]
    _ = Pm * (X * Y) * Pi := by
        rw [h, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem conj_conj_aux (Pm Pi X : Matrix (Fin 2) (Fin 2) K) (h : Pi * Pm = 1) :
    Pi * (Pm * X * Pi) * Pm = X := by
  calc Pi * (Pm * X * Pi) * Pm = (Pi * Pm) * X * (Pi * Pm) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [h, Matrix.one_mul, Matrix.mul_one]

@[expose] def conjSL (P : GL (Fin 2) K) : SL(2, K) →* SL(2, K) where
  toFun x := ⟨(P : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
      ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
    rw [Matrix.det_mul, Matrix.det_mul, x.2, mul_one, ← Matrix.det_mul, mul_glInv,
      Matrix.det_one]⟩
  map_one' := by
    apply Subtype.ext
    show (P : Matrix (Fin 2) (Fin 2) K) * (1 : Matrix (Fin 2) (Fin 2) K) *
      ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.mul_one, mul_glInv]
  map_mul' x y := Subtype.ext (conj_mul_aux _ _ _ _ (glInv_mul P))

theorem coe_conjSL (P : GL (Fin 2) K) (x : SL(2, K)) :
    ((conjSL P x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (P : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
        ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem conjSL_inv_conjSL (P : GL (Fin 2) K) (x : SL(2, K)) : conjSL P⁻¹ (conjSL P x) = x := by
  apply Subtype.ext
  rw [coe_conjSL, coe_conjSL, inv_inv]
  exact conj_conj_aux _ _ _ (glInv_mul P)

theorem conjSL_of_mem_center (P : GL (Fin 2) K) {c : SL(2, K)}
    (hc : c ∈ Subgroup.center SL(2, K)) : conjSL P c = c := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  apply Subtype.ext
  rw [coe_conjSL, ← hr]
  have : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) K) =
      r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, mul_glInv]

theorem conjSL_mem_center_iff (P : GL (Fin 2) K) (x : SL(2, K)) :
    conjSL P x ∈ Subgroup.center SL(2, K) ↔ x ∈ Subgroup.center SL(2, K) := by
  constructor
  · intro h
    have := conjSL_of_mem_center P⁻¹ h
    rw [conjSL_inv_conjSL] at this
    rw [this]
    exact h
  · intro h
    rw [conjSL_of_mem_center P h]
    exact h

theorem conjSL_eq_of_mul_eq (P : GL (Fin 2) K) {u g : SL(2, K)}
    (h : (P : Matrix (Fin 2) (Fin 2) K) * (u : Matrix (Fin 2) (Fin 2) K) =
      (g : Matrix (Fin 2) (Fin 2) K) * (P : Matrix (Fin 2) (Fin 2) K)) : conjSL P u = g := by
  apply Subtype.ext
  rw [coe_conjSL, h, Matrix.mul_assoc, mul_glInv, Matrix.mul_one]

end Conj

section Cyclic

variable {K : Type} [Field K]

theorem exists_cyclic (M : Matrix (Fin 2) (Fin 2) K) (hM : M * M + M + 1 = 0)
    (hns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ P : Matrix (Fin 2) (Fin 2) K, P.det ≠ 0 ∧ M * P = P * !![0, -1; 1, -1] := by
  have hMv : ∀ v : Fin 2 → K, M *ᵥ (M *ᵥ v) + M *ᵥ v + v = 0 := by
    intro v
    have := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X *ᵥ v) hM
    simpa [Matrix.add_mulVec, Matrix.mulVec_mulVec] using this
  have hv : ∃ v : Fin 2 → K, v 0 * (M *ᵥ v) 1 - (M *ᵥ v) 0 * v 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon ![1, 0]
    have e2 := hcon ![0, 1]
    have e3 := hcon ![1, 1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2 e3
    apply hns (M 0 0)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    all_goals first | linear_combination e1 | linear_combination e2 |
      linear_combination e3 - e1 + e2
  obtain ⟨v, hv⟩ := hv
  refine ⟨!![v 0, (M *ᵥ v) 0; v 1, (M *ᵥ v) 1], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    exact hv
  · have h0 := congrFun (hMv v) 0
    have h1 := congrFun (hMv v) 1
    simp only [Pi.add_apply, Pi.zero_apply] at h0 h1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] at h0 h1 ⊢
    all_goals first | ring1 | linear_combination h0 | linear_combination h1

theorem exists_conj (M N : Matrix (Fin 2) (Fin 2) K) (hM : M * M + M + 1 = 0)
    (hN : N * N + N + 1 = 0) (hMns : ∀ c : K, M ≠ c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hNns : ∀ c : K, N ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ Q : GL (Fin 2) K,
      (Q : Matrix (Fin 2) (Fin 2) K) * M = N * (Q : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨PM, hPM, hMP⟩ := exists_cyclic M hM hMns
  obtain ⟨PN, hPN, hNP⟩ := exists_cyclic N hN hNns
  let GM : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero PM hPM
  let GN : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero PN hPN
  have hGM : (GM : Matrix (Fin 2) (Fin 2) K) = PM := rfl
  have hGN : (GN : Matrix (Fin 2) (Fin 2) K) = PN := rfl
  refine ⟨GN * GM⁻¹, ?_⟩
  set Pi : Matrix (Fin 2) (Fin 2) K := ((GM⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hPi
  have hPiPM : Pi * PM = 1 := by rw [← hGM]; exact glInv_mul GM
  have hPMPi : PM * Pi = 1 := by rw [← hGM]; exact mul_glInv GM
  have h1 : Pi * M = !![0, -1; 1, -1] * Pi := by
    calc Pi * M = Pi * M * (PM * Pi) := by rw [hPMPi, Matrix.mul_one]
      _ = Pi * (M * PM) * Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * (PM * !![0, -1; 1, -1]) * Pi := by rw [hMP]
      _ = (Pi * PM) * !![0, -1; 1, -1] * Pi := by simp only [Matrix.mul_assoc]
      _ = !![0, -1; 1, -1] * Pi := by rw [hPiPM, Matrix.one_mul]
  rw [Units.val_mul, hGN]
  calc PN * Pi * M = PN * (Pi * M) := Matrix.mul_assoc _ _ _
    _ = PN * (!![0, -1; 1, -1] * Pi) := by rw [h1]
    _ = (PN * !![0, -1; 1, -1]) * Pi := (Matrix.mul_assoc _ _ _).symm
    _ = (N * PN) * Pi := by rw [← hNP]
    _ = N * (PN * Pi) := Matrix.mul_assoc _ _ _

end Cyclic

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
