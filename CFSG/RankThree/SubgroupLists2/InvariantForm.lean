module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.RankThree.SubgroupLists.RationalElements
import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K]

@[expose] def jordanThree (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 0; 0, 1, 1; 0, 0, 1]

@[expose] def jordanThreeInv (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![1, -1, 1; 0, 1, -1; 0, 0, 1]

@[expose] def formThree (D : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, -4; 0, 4, -2; -4, -2, D]

theorem jordanThreeInv_mul_jordanThree : jordanThreeInv K * jordanThree K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThree, jordanThreeInv, Matrix.mul_apply, Fin.sum_univ_three]

theorem formThree_transpose (D : K) : (formThree D)ᵀ = formThree D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formThree]

theorem det_formThree (D : K) : (formThree D).det = -64 := by
  simp [formThree, Matrix.det_fin_three]
  norm_num

theorem jordanThree_transpose_mul_formThree_mul (D : K) :
    (jordanThree K)ᵀ * formThree D * jordanThree K = formThree D := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanThree, formThree, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem trace_jordanThree_mul (w : Matrix (Fin 3) (Fin 3) K) :
    (jordanThree K * w).trace = w.trace + w 1 0 + w 2 1 := by
  rw [Matrix.trace_fin_three, Matrix.trace_fin_three]
  simp [jordanThree, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem trace_mul_jordanThreeInv (w : Matrix (Fin 3) (Fin 3) K) :
    (w * jordanThreeInv K).trace = w.trace - w 1 0 + w 2 0 - w 2 1 := by
  rw [Matrix.trace_fin_three, Matrix.trace_fin_three]
  simp [jordanThreeInv, Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem transpose_mul_formThree_mul_of_involution {w : Matrix (Fin 3) (Fin 3) K}
    (hw : w * w = 1) (htr : w.trace = -1) (hJ : (jordanThree K * w).trace = 0)
    (hJi : (w * jordanThreeInv K).trace = 0) :
    wᵀ * formThree (2 * (w 0 0 - w 2 2) + w 1 0) * w =
      formThree (2 * (w 0 0 - w 2 2) + w 1 0) := by
  rw [trace_jordanThree_mul, htr] at hJ
  rw [trace_mul_jordanThreeInv, htr] at hJi
  have h1 : w 1 0 + w 2 1 = 1 := by linear_combination hJ
  have h2 : w 2 0 = 2 := by linear_combination hJi + hJ
  rw [Matrix.trace_fin_three] at htr
  have e : ∀ r s, (w * w) r s = (1 : Matrix (Fin 3) (Fin 3) K) r s := fun r s => by rw [hw]
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.isValue, ↓reduceIte,
    Fin.reduceEq] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext r s
  fin_cases r <;> fin_cases s <;> simp [formThree, Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination (-2 * (w 2 0)) * e20 +
      (4 * (w 0 0) * (w 2 0) + (w 1 0) * (w 2 0) + 2 * (w 1 0) * (w 2 1) - 2 * (w 1 0)) * h2 +
      (4 * (w 1 0)) * h1
  · linear_combination (-4) * e21 + (-2 * (w 2 0) * (w 2 1) + 4 * (w 2 1)) * htr +
      (4 * (w 0 0) * (w 2 1) + (w 1 0) * (w 2 1) + 2 * (w 1 1) * (w 2 1) - 2 * (w 1 1) +
        2 * (w 2 1)) * h2 + (4 * (w 1 1)) * h1
  · linear_combination (-2 * (w 2 1)) * e10 + (2 * (w 2 0)) * e11 +
      (-2 * (w 0 0) - 2 * (w 2 2) - 4) * e20 + (-2 * (w 1 0)) * e21 + (-4) * e22 +
      (6 * (w 0 0) * (w 2 0) - 8 * (w 0 0) + (w 1 0) * (w 2 0) + 4 * (w 1 0) * (w 2 1) -
        2 * (w 1 0) - 4 * (w 1 1) + 4 * (w 2 0) + 4 * (w 2 2) - 4) * htr +
      (-4 * (w 0 0) ^ 2 - (w 0 0) * (w 1 0) - 6 * (w 0 0) * (w 1 1) - 6 * (w 0 0) -
        (w 1 0) * (w 1 1) - (w 1 0) - 2 * (w 1 1) ^ 2 - 4 * (w 1 1) - 2 * (w 1 2) - 2) * h2 +
      (4 * (w 1 2)) * h1
  · linear_combination (-4) * e21 + (-2 * (w 2 0) * (w 2 1) + 4 * (w 2 1)) * htr +
      (4 * (w 0 0) * (w 2 1) + (w 1 0) * (w 2 1) + 2 * (w 1 1) * (w 2 1) - 2 * (w 1 1) +
        2 * (w 2 1)) * h2 + (4 * (w 1 1)) * h1
  · linear_combination (-2 * (w 2 1)) * e10 + (2 * (w 2 0)) * e11 + (w 2 1) * e20 +
      (-2 * (w 1 0) - 4 * (w 2 1)) * e21 +
      (2 * (w 1 0) * (w 2 1) - (w 2 0) * (w 2 1) + 2 * (w 2 1) ^ 2) * htr +
      (4 * (w 0 1) * (w 2 1) - 2 * (w 1 1) ^ 2 + (w 1 1) * (w 2 1) + (w 2 1) + 2) * h2 +
      (2 * (w 1 1) * (w 2 1) - 2 * (w 2 1)) * h1
  · linear_combination (2 - 2 * (w 2 1)) * e00 + (2 * (w 2 0) - 8) * e01 +
      (-2 * (w 0 0) + 2 * (w 1 1) - (w 2 1) - 2) * e10 + ((w 2 0) - 2) * e11 + (-4) * e12 +
      (-(w 0 0) + 2 * (w 0 1) - 2) * e20 +
      (2 * (w 0 0) - (w 1 0) + 4 * (w 1 1) - 2 * (w 2 2) + 2) * e21 +
      ((w 0 0) * (w 2 0) - 4 * (w 0 1) + 2 * (w 1 0) * (w 2 1) - 2 * (w 1 1) * (w 2 1) -
        2 * (w 1 1) + 4 * (w 1 2) + 2 * (w 2 0) - 2 * (w 2 1)) * htr +
      (-6 * (w 0 0) * (w 0 1) - (w 0 0) * (w 1 1) + 2 * (w 0 0) * (w 1 2) - (w 0 0) -
        6 * (w 0 1) * (w 1 1) - 2 * (w 0 1) - 2 * (w 0 2) - (w 1 1) ^ 2 -
        2 * (w 1 1) * (w 1 2) - 2 * (w 1 1) + 2 * (w 1 2) - 1) * h2 +
      (2 * (w 0 0) ^ 2 + 2 * (w 0 0) + 4 * (w 0 2) - 2 * (w 1 1) ^ 2 + 2 * (w 1 1)) * h1
  · linear_combination (-2 * (w 2 1)) * e10 + (2 * (w 2 0)) * e11 +
      (-2 * (w 0 0) - 2 * (w 2 2) - 4) * e20 + (-2 * (w 1 0)) * e21 + (-4) * e22 +
      (6 * (w 0 0) * (w 2 0) - 8 * (w 0 0) + (w 1 0) * (w 2 0) + 4 * (w 1 0) * (w 2 1) -
        2 * (w 1 0) - 4 * (w 1 1) + 4 * (w 2 0) + 4 * (w 2 2) - 4) * htr +
      (-4 * (w 0 0) ^ 2 - (w 0 0) * (w 1 0) - 6 * (w 0 0) * (w 1 1) - 6 * (w 0 0) -
        (w 1 0) * (w 1 1) - (w 1 0) - 2 * (w 1 1) ^ 2 - 4 * (w 1 1) - 2 * (w 1 2) - 2) * h2 +
      (4 * (w 1 2)) * h1
  · linear_combination (2 - 2 * (w 2 1)) * e00 + (2 * (w 2 0) - 8) * e01 +
      (-2 * (w 0 0) + 2 * (w 1 1) - (w 2 1) - 2) * e10 + ((w 2 0) - 2) * e11 + (-4) * e12 +
      (-(w 0 0) + 2 * (w 0 1) - 2) * e20 +
      (2 * (w 0 0) - (w 1 0) + 4 * (w 1 1) - 2 * (w 2 2) + 2) * e21 +
      ((w 0 0) * (w 2 0) - 4 * (w 0 1) + 2 * (w 1 0) * (w 2 1) - 2 * (w 1 1) * (w 2 1) -
        2 * (w 1 1) + 4 * (w 1 2) + 2 * (w 2 0) - 2 * (w 2 1)) * htr +
      (-6 * (w 0 0) * (w 0 1) - (w 0 0) * (w 1 1) + 2 * (w 0 0) * (w 1 2) - (w 0 0) -
        6 * (w 0 1) * (w 1 1) - 2 * (w 0 1) - 2 * (w 0 2) - (w 1 1) ^ 2 -
        2 * (w 1 1) * (w 1 2) - 2 * (w 1 1) + 2 * (w 1 2) - 1) * h2 +
      (2 * (w 0 0) ^ 2 + 2 * (w 0 0) + 4 * (w 0 2) - 2 * (w 1 1) ^ 2 + 2 * (w 1 1)) * h1
  · linear_combination (w 1 0) * e00 + (-2 * (w 1 0)) * e01 + (2 * (w 2 0) - 8) * e02 +
      ((w 0 0) + 2 * (w 0 1) + 3 * (w 1 1) + 2 * (w 1 2) + 2 * (w 2 2) + 2) * e10 +
      (-(w 1 0)) * e11 + (-2 * (w 2 0) + 2 * (w 2 1)) * e12 +
      (2 * (w 0 0) + (w 1 0) - 2 * (w 2 2)) * e22 +
      (-2 * (w 0 0) * (w 1 0) - 2 * (w 1 0) * (w 1 1) - 4 * (w 1 2)) * htr +
      (-4 * (w 0 0) * (w 0 2) - (w 0 0) * (w 1 2) - 4 * (w 0 1) * (w 1 2) -
        (w 1 1) * (w 1 2) - 2 * (w 1 2) ^ 2 - 2 * (w 1 2)) * h2 +
      (-2 * (w 0 0) * (w 1 2) - 2 * (w 1 1) * (w 1 2)) * h1

theorem trace_eq_zero_of_pow_three_eq_one {g : GL (Fin 3) K}
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) (hg3 : g ^ 3 = 1)
    (hns : ∀ c : K, (g : Matrix (Fin 3) (Fin 3) K) ≠ Matrix.scalar (Fin 3) c) :
    (g : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  set G := (g : Matrix (Fin 3) (Fin 3) K) with hG
  set σ := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace with hσdef
  have hG3 : G ^ 3 = 1 := by rw [hG, ← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  have hCH := cayley_hamilton_sl3 g hdet
  rw [← hG, ← hσdef, hG3, eq_comm, add_eq_right, sub_eq_zero] at hCH
  have h2 : σ • G ^ 2 = G.trace • (1 : Matrix (Fin 3) (Fin 3) K) := by
    calc σ • G ^ 2 = (σ • G) * G := by rw [smul_mul_assoc, sq]
      _ = (G.trace • G ^ 2) * G := by rw [hCH]
      _ = G.trace • (1 : Matrix (Fin 3) (Fin 3) K) := by
          rw [smul_mul_assoc, ← pow_succ, hG3]
  by_cases hσ : σ = 0
  · rw [hσ, zero_smul] at h2
    have := congrFun (congrFun h2 0) 0
    simpa using this.symm
  · exfalso
    set c := G.trace / σ with hc
    have hGG : G ^ 2 = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hc, div_eq_inv_mul, mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hσ, one_smul]
    apply hns (c * c)
    calc G = G ^ 3 * G := by rw [hG3, Matrix.one_mul]
      _ = G ^ 2 * G ^ 2 := by rw [← pow_succ, ← pow_add]
      _ = Matrix.scalar (Fin 3) (c * c) := by
        rw [hGG, smul_mul_smul_comm, Matrix.one_mul, Matrix.scalar_apply,
          ← smul_one_eq_diagonal]

theorem trace_eq_neg_one_of_involution (h2 : (2 : K) ≠ 0) {t : GL (Fin 3) K} (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hdet : (t : Matrix (Fin 3) (Fin 3) K).det = 1) :
    (t : Matrix (Fin 3) (Fin 3) K).trace = -1 := by
  obtain ⟨P, hP⟩ := exists_conj_negDiag3 h2 ht2 ht1 hdet
  have h : (t : Matrix (Fin 3) (Fin 3) K).trace =
      ((negDiag3 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace :=
    trace_eq_of_isConj (isConj_iff.mpr ⟨P⁻¹, by rw [inv_inv]; exact hP⟩)
  rw [h, coe_negDiag3, Matrix.trace_diagonal, Fin.sum_univ_three]
  norm_num

theorem exists_mul_eq_mul_jordanThree {X : Matrix (Fin 3) (Fin 3) K} (h3 : (X - 1) ^ 3 = 0)
    (h2 : (X - 1) ^ 2 ≠ 0) :
    ∃ P : Matrix (Fin 3) (Fin 3) K, P.det ≠ 0 ∧ X * P = P * jordanThree K := by
  classical
  set N := X - 1 with hN
  obtain ⟨v, hv⟩ : ∃ v, N ^ 2 *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply h2
    exact Matrix.ext_of_mulVec_single fun j => by rw [h, zero_mulVec]
  set f : Fin 3 → Fin 3 → K := ![N ^ 2 *ᵥ v, N *ᵥ v, v] with hf
  set P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => f j i with hP
  have hN3v : N *ᵥ (N ^ 2 *ᵥ v) = 0 := by
    rw [mulVec_mulVec, ← pow_succ', h3, zero_mulVec]
  have hN2v : N *ᵥ (N *ᵥ v) = N ^ 2 *ᵥ v := by rw [mulVec_mulVec, sq]
  have hXv : ∀ u : Fin 3 → K, X *ᵥ u = u + N *ᵥ u := by
    intro u
    rw [hN, sub_mulVec, one_mulVec]
    abel
  have hPc : ∀ c : Fin 3 → K, P *ᵥ c = c 0 • f 0 + c 1 • f 1 + c 2 • f 2 := by
    intro c
    ext i
    simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
  refine ⟨P, ?_, ?_⟩
  · intro h0
    obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hPc] at hc
    have hN2f0 : N ^ 2 *ᵥ f 0 = 0 := by
      simp only [hf, Matrix.cons_val_zero]
      rw [mulVec_mulVec, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_succ, h3, zero_mul,
        zero_mulVec]
    have hN2f1 : N ^ 2 *ᵥ f 1 = 0 := by
      simp only [hf, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [mulVec_mulVec, ← pow_succ, h3, zero_mulVec]
    have hNf0 : N *ᵥ f 0 = 0 := by simpa [hf] using hN3v
    have hNf1 : N *ᵥ f 1 = N ^ 2 *ᵥ v := by simpa [hf] using hN2v
    have hc2 : c 2 = 0 := by
      have h := congrArg (fun u => N ^ 2 *ᵥ u) hc
      simp only [mulVec_add, mulVec_smul, hN2f0, hN2f1, smul_zero, zero_add, mulVec_zero] at h
      have hf2 : f 2 = v := by simp [hf]
      rw [hf2] at h
      exact (smul_eq_zero.mp h).resolve_right hv
    have hc1 : c 1 = 0 := by
      have h := congrArg (fun u => N *ᵥ u) hc
      simp only [mulVec_add, mulVec_smul, hNf0, hNf1, hc2, zero_smul, smul_zero, zero_add,
        add_zero, mulVec_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hv
    have hc0 : c 0 = 0 := by
      rw [hc1, hc2, zero_smul, zero_smul, add_zero, add_zero] at hc
      have hf0 : f 0 = N ^ 2 *ᵥ v := by simp [hf]
      rw [hf0] at hc
      exact (smul_eq_zero.mp hc).resolve_right hv
    apply hcne
    funext i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  · have hcol : ∀ j, (X * P) *ᵥ Pi.single j 1 = X *ᵥ f j := by
      intro j
      rw [← mulVec_mulVec, mulVec_single_one]
      congr 1
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [hcol, ← mulVec_mulVec, hXv, hPc]
    fin_cases j
    · simp [jordanThree, hf, hN3v]
    · simp [jordanThree, hf, hN2v]
      exact add_comm _ _
    · simp [jordanThree, hf]
      exact add_comm _ _

theorem transpose_mul_conj_form {P Pi G B : Matrix (Fin 3) (Fin 3) K}
    (hP : P * Pi = 1) (hB : (Pi * G * P)ᵀ * B * (Pi * G * P) = B) :
    Gᵀ * (Piᵀ * B * Pi) * G = Piᵀ * B * Pi := by
  have h1 : Pi * G = (Pi * G * P) * Pi := by rw [Matrix.mul_assoc _ P, hP, Matrix.mul_one]
  calc Gᵀ * (Piᵀ * B * Pi) * G = (Pi * G)ᵀ * B * (Pi * G) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((Pi * G * P) * Pi)ᵀ * B * ((Pi * G * P) * Pi) := by rw [← h1]
    _ = Piᵀ * ((Pi * G * P)ᵀ * B * (Pi * G * P)) * Pi := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Piᵀ * B * Pi := by rw [hB]

theorem jordanThree_mul_ne_scalar (h2 : (2 : K) ≠ 0) {w : Matrix (Fin 3) (Fin 3) K}
    (hw : w * w = 1) (c : K) : jordanThree K * w ≠ Matrix.scalar (Fin 3) c := by
  intro h
  have hw' : w = c • jordanThreeInv K := by
    calc w = jordanThreeInv K * (jordanThree K * w) := by
          rw [← Matrix.mul_assoc, jordanThreeInv_mul_jordanThree, Matrix.one_mul]
      _ = c • jordanThreeInv K := by
          rw [h, Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rw [hw'] at hw
  have h00 := congrFun (congrFun hw 0) 0
  have h01 := congrFun (congrFun hw 0) 1
  simp [jordanThreeInv, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01
  apply h2
  linear_combination (-1 : K) * h01 - 2 * h00

theorem exists_invariant_symmetric_form (h2 : (2 : K) ≠ 0) {x w : GL (Fin 3) K}
    (hx3 : ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 3 = 0)
    (hx2 : ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 2 ≠ 0)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hdetw : (w : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hxw : (x * w) ^ 3 = 1) :
    ∃ M : Matrix (Fin 3) (Fin 3) K, Mᵀ = M ∧ M.det ≠ 0 ∧
      (x : Matrix (Fin 3) (Fin 3) K)ᵀ * M * x = M ∧
      (w : Matrix (Fin 3) (Fin 3) K)ᵀ * M * w = M := by
  classical
  set X := (x : Matrix (Fin 3) (Fin 3) K) with hX
  set W := (w : Matrix (Fin 3) (Fin 3) K) with hW
  set Xi := ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hXi
  obtain ⟨P, hPdet, hXP⟩ := exists_mul_eq_mul_jordanThree hx3 hx2
  set Pg := GeneralLinearGroup.mkOfDetNeZero P hPdet with hPg
  set Pi := ((Pg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hPi
  have hPPi : P * Pi = 1 := by
    rw [hPi, show P = (Pg : Matrix (Fin 3) (Fin 3) K) from rfl, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hPiP : Pi * P = 1 := by
    rw [hPi, show P = (Pg : Matrix (Fin 3) (Fin 3) K) from rfl, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hconj : ∀ A B : Matrix (Fin 3) (Fin 3) K,
      (Pi * A * P) * (Pi * B * P) = Pi * (A * B) * P := by
    intro A B
    calc Pi * A * P * (Pi * B * P) = Pi * A * (P * Pi) * B * P := by
          simp only [Matrix.mul_assoc]
      _ = Pi * (A * B) * P := by rw [hPPi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have htrconj : ∀ A : Matrix (Fin 3) (Fin 3) K, (Pi * A * P).trace = A.trace := by
    intro A
    rw [Matrix.trace_mul_cycle, hPPi, Matrix.one_mul]
  have hdetconj : ∀ A : Matrix (Fin 3) (Fin 3) K, (Pi * A * P).det = A.det := by
    intro A
    rw [det_mul, det_mul, mul_comm Pi.det, mul_assoc, ← det_mul, hPiP, det_one, mul_one]
  have hJ : Pi * X * P = jordanThree K := by
    rw [Matrix.mul_assoc, hXP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hXXi : X * Xi = 1 := by rw [hX, hXi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJi : Pi * Xi * P = jordanThreeInv K := by
    have h1 : jordanThree K * (Pi * Xi * P) = 1 := by
      rw [← hJ, hconj, hXXi, Matrix.mul_one, hPiP]
    calc Pi * Xi * P = jordanThreeInv K * jordanThree K * (Pi * Xi * P) := by
          rw [jordanThreeInv_mul_jordanThree, Matrix.one_mul]
      _ = jordanThreeInv K := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hdetx : X.det = 1 := by
    rw [← hdetconj, hJ]
    simp [jordanThree, Matrix.det_fin_three]
  have hWW : W * W = 1 := by rw [hW, ← Units.val_mul, hw2, Units.val_one]
  set w' := Pi * W * P with hw'
  have hww : w' * w' = 1 := by rw [hw', hconj, hWW, Matrix.mul_one, hPiP]
  have hscal : ∀ (A : Matrix (Fin 3) (Fin 3) K) (c : K), A = Matrix.scalar (Fin 3) c →
      Pi * A * P = Matrix.scalar (Fin 3) c := by
    rintro A c rfl
    rw [Matrix.mul_assoc, (Matrix.scalar_commute c (fun _ => mul_comm _ _) P).eq,
      ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hns : ∀ c : K, ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      Matrix.scalar (Fin 3) c := by
    intro c hc
    have h := hscal _ c hc
    rw [Units.val_mul, ← hconj, hJ] at h
    exact jordanThree_mul_ne_scalar h2 hww c h
  have hns' : ∀ c : K, (((x * w)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      Matrix.scalar (Fin 3) c := by
    intro c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      have h := congrArg Matrix.det hc
      rw [map_zero, Matrix.det_zero] at h
      exact (Matrix.isUnits_det_units ((x * w)⁻¹)).ne_zero h
    apply hns c⁻¹
    have h1 : ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((x * w)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hc] at h1
    calc ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Matrix.scalar (Fin 3) c *
            Matrix.scalar (Fin 3) c⁻¹ := by
          rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, Matrix.mul_one]
      _ = Matrix.scalar (Fin 3) c⁻¹ := by rw [h1, Matrix.one_mul]
  have hdetxw : ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, det_mul, hdetx, hdetw, one_mul]
  have hdetxw' : (((x * w)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h := congrArg Matrix.det (show ((x * w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((x * w)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    rwa [det_mul, hdetxw, one_mul, det_one] at h
  have htrxw : (X * W).trace = 0 := by
    have h := trace_eq_zero_of_pow_three_eq_one hdetxw hxw hns
    rwa [Units.val_mul] at h
  have hwinv : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  have htrwxi : (W * Xi).trace = 0 := by
    have hinv : (x * w)⁻¹ = w * x⁻¹ := by rw [_root_.mul_inv_rev, hwinv]
    have h := trace_eq_zero_of_pow_three_eq_one hdetxw' (by rw [inv_pow, hxw, inv_one]) hns'
    rwa [hinv, Units.val_mul] at h
  have htrw : W.trace = -1 := trace_eq_neg_one_of_involution h2 hw2 hw1 hdetw
  have htrw' : w'.trace = -1 := by rw [hw', htrconj, htrw]
  have htrJw : (jordanThree K * w').trace = 0 := by rw [← hJ, hw', hconj, htrconj, htrxw]
  have htrwJi : (w' * jordanThreeInv K).trace = 0 := by
    rw [← hJi, hw', hconj, htrconj, htrwxi]
  have hform := transpose_mul_formThree_mul_of_involution hww htrw' htrJw htrwJi
  set D := 2 * (w' 0 0 - w' 2 2) + w' 1 0
  refine ⟨Piᵀ * formThree D * Pi, ?_, ?_,
    transpose_mul_conj_form hPPi (by rw [hJ]; exact jordanThree_transpose_mul_formThree_mul D),
    transpose_mul_conj_form hPPi hform⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      formThree_transpose, Matrix.mul_assoc]
  · have hPidet : Pi.det ≠ 0 := by
      intro h0
      have h := congrArg Matrix.det hPPi
      rw [det_mul, h0, mul_zero, det_one] at h
      exact zero_ne_one h
    have h64 : (64 : K) ≠ 0 := by
      have : (64 : K) = 2 ^ 6 := by norm_num
      rw [this]
      exact pow_ne_zero 6 h2
    rw [det_mul, det_mul, det_transpose, det_formThree]
    exact mul_ne_zero (mul_ne_zero hPidet (neg_ne_zero.mpr h64)) hPidet

end CFSG.RankThree.SubgroupLists
