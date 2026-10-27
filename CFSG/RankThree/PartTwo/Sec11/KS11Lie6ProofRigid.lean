module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofTheta

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
open scoped MatrixGroups

section Matrices

variable {L : Type} [Field L]

theorem trace_diagConj (b : Lˣ) (A : SL2 L) :
    Matrix.trace ((diagConj b A : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) L) := by
  simp [coe_diagConj, diagConjMat, Matrix.trace_fin_two]

theorem diagConj_eq_self_of_sign {b : Lˣ} {A : SL2 L}
    (h : diagConj b A * A⁻¹ = 1 ∨ diagConj b A * A⁻¹ = -1)
    (htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) L) = 2) : diagConj b A = A := by
  rcases h with h | h
  · exact mul_inv_eq_one.1 h
  · have h1 : diagConj b A = -A := by
      calc diagConj b A = diagConj b A * A⁻¹ * A := by group
        _ = -A := by rw [h, neg_one_mul]
    have h2 := trace_diagConj b A
    rw [h1, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg, htr] at h2
    have h22 : (2 : L) = 0 := by
      have h4 : (2 : L) * 2 = 0 := by linear_combination -h2
      exact (mul_self_eq_zero.1 h4)
    rw [h1]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_neg]
    ext i j
    have : (A : Matrix (Fin 2) (Fin 2) L) i j + (A : Matrix (Fin 2) (Fin 2) L) i j = 0 := by
      linear_combination (A : Matrix (Fin 2) (Fin 2) L) i j * h22
    rw [Matrix.neg_apply]
    linear_combination -this

theorem eq_one_of_diagConj_eq {b : Lˣ} {A B : SL2 L} (hA : diagConj b A = A)
    (hB : diagConj b B = B) (hAB : A * B ≠ B * A) : b = 1 := by
  by_contra hb
  have hb1 : (b : L) - 1 ≠ 0 := by
    intro h
    exact hb (Units.ext (by rw [Units.val_one]; linear_combination h))
  have hb2 : ((b⁻¹ : Lˣ) : L) - 1 ≠ 0 := by
    intro h
    apply hb
    have : b⁻¹ = 1 := Units.ext (by rw [Units.val_one]; linear_combination h)
    rw [← inv_inv b, this, inv_one]
  have off : ∀ X : SL2 L, diagConj b X = X →
      (X : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧ (X : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    intro X hX
    have h01 := congrArg (fun Y : SL2 L => (Y : Matrix (Fin 2) (Fin 2) L) 0 1) hX
    have h10 := congrArg (fun Y : SL2 L => (Y : Matrix (Fin 2) (Fin 2) L) 1 0) hX
    simp only [coe_diagConj, diagConjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h01 h10
    refine ⟨?_, ?_⟩
    · have : ((b : L) - 1) * (X : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
        linear_combination h01
      exact (mul_eq_zero.1 this).resolve_left hb1
    · have : (((b⁻¹ : Lˣ) : L) - 1) * (X : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
        linear_combination h10
      exact (mul_eq_zero.1 this).resolve_left hb2
  obtain ⟨a01, a10⟩ := off A hA
  obtain ⟨b01, b10⟩ := off B hB
  apply hAB
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, a01, a10, b01, b10, mul_comm]

theorem trace_conj_SL2 (P X : SL2 L) :
    Matrix.trace ((P⁻¹ * X * P : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.trace (X : Matrix (Fin 2) (Fin 2) L) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem trace_uSL_one : Matrix.trace ((uSL 1 : SL2 L) : Matrix (Fin 2) (Fin 2) L) = 2 := by
  simp [coe_uSL, Matrix.trace_fin_two]
  norm_num

theorem trace_vSL_one : Matrix.trace ((vSL 1 : SL2 L) : Matrix (Fin 2) (Fin 2) L) = 2 := by
  simp [coe_vSL, Matrix.trace_fin_two]
  norm_num

theorem uSL_mul_vSL_ne : (uSL 1 : SL2 L) * vSL 1 ≠ vSL 1 * uSL 1 := by
  intro h
  have h00 := congrArg (fun Y : SL2 L => (Y : Matrix (Fin 2) (Fin 2) L) 0 0) h
  simp [coe_uSL, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem conj_uSL_mul_conj_vSL_ne (P : SL2 L) :
    P⁻¹ * uSL 1 * P * (P⁻¹ * vSL 1 * P) ≠ P⁻¹ * vSL 1 * P * (P⁻¹ * uSL 1 * P) := by
  intro h
  apply uSL_mul_vSL_ne (L := L)
  have h' : P * (P⁻¹ * uSL 1 * P * (P⁻¹ * vSL 1 * P)) * P⁻¹ =
      P * (P⁻¹ * vSL 1 * P * (P⁻¹ * uSL 1 * P)) * P⁻¹ := by rw [h]
  simpa [mul_assoc] using h'

theorem eq_one_of_diagConj_sign (P : SL2 L) {b : Lˣ}
    (hu : diagConj b (P⁻¹ * uSL 1 * P) * (P⁻¹ * uSL 1 * P)⁻¹ = 1 ∨
      diagConj b (P⁻¹ * uSL 1 * P) * (P⁻¹ * uSL 1 * P)⁻¹ = -1)
    (hv : diagConj b (P⁻¹ * vSL 1 * P) * (P⁻¹ * vSL 1 * P)⁻¹ = 1 ∨
      diagConj b (P⁻¹ * vSL 1 * P) * (P⁻¹ * vSL 1 * P)⁻¹ = -1) : b = 1 :=
  eq_one_of_diagConj_eq (diagConj_eq_self_of_sign hu (by rw [trace_conj_SL2, trace_uSL_one]))
    (diagConj_eq_self_of_sign hv (by rw [trace_conj_SL2, trace_vSL_one]))
    (conj_uSL_mul_conj_vSL_ne P)

end Matrices

section Torus

variable
  {L : Type} [Field L]

theorem rootDiagUnit_conj_outerTriple (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (X : SL2 L × SL2 L × SL2 L) :
    rootDiagUnit TwistTag.D4.tag b * outerTriple L X * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
      outerTriple L (diagConj (b n0) X.1, diagConj (b n1) X.2.1, diagConj (b n3) X.2.2) := by
  rw [outerTriple_apply, outerTriple_apply, ← rootDiagUnit_conj_rankOneHom,
    ← rootDiagUnit_conj_rankOneHom, ← rootDiagUnit_conj_rankOneHom]
  group

theorem eq_mulSingle_of_commute (P : SL2 L × SL2 L × SL2 L) {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hu : rootDiagUnit TwistTag.D4.tag b * outerTriple L (P⁻¹ * (uSL 1, uSL 1, uSL 1) * P) =
      outerTriple L (P⁻¹ * (uSL 1, uSL 1, uSL 1) * P) * rootDiagUnit TwistTag.D4.tag b)
    (hv : rootDiagUnit TwistTag.D4.tag b * outerTriple L (P⁻¹ * (vSL 1, vSL 1, vSL 1) * P) =
      outerTriple L (P⁻¹ * (vSL 1, vSL 1, vSL 1) * P) * rootDiagUnit TwistTag.D4.tag b) :
    b = Pi.mulSingle n2 (b n2) := by
  have key : ∀ x : SL2 L, rootDiagUnit TwistTag.D4.tag b * outerTriple L (P⁻¹ * (x, x, x) * P) =
      outerTriple L (P⁻¹ * (x, x, x) * P) * rootDiagUnit TwistTag.D4.tag b →
      outerTriple L (diagConj (b n0) (P.1⁻¹ * x * P.1) * (P.1⁻¹ * x * P.1)⁻¹,
        diagConj (b n1) (P.2.1⁻¹ * x * P.2.1) * (P.2.1⁻¹ * x * P.2.1)⁻¹,
        diagConj (b n3) (P.2.2⁻¹ * x * P.2.2) * (P.2.2⁻¹ * x * P.2.2)⁻¹) = 1 := by
    intro x hx
    have h1 : rootDiagUnit TwistTag.D4.tag b * outerTriple L (P⁻¹ * (x, x, x) * P) *
        (rootDiagUnit TwistTag.D4.tag b)⁻¹ = outerTriple L (P⁻¹ * (x, x, x) * P) := by
      rw [hx, mul_inv_cancel_right]
    rw [rootDiagUnit_conj_outerTriple] at h1
    have h2 : (P⁻¹ * (x, x, x) * P : SL2 L × SL2 L × SL2 L) =
        (P.1⁻¹ * x * P.1, P.2.1⁻¹ * x * P.2.1, P.2.2⁻¹ * x * P.2.2) := rfl
    rw [h2] at h1
    rw [show (diagConj (b n0) (P.1⁻¹ * x * P.1) * (P.1⁻¹ * x * P.1)⁻¹,
        diagConj (b n1) (P.2.1⁻¹ * x * P.2.1) * (P.2.1⁻¹ * x * P.2.1)⁻¹,
        diagConj (b n3) (P.2.2⁻¹ * x * P.2.2) * (P.2.2⁻¹ * x * P.2.2)⁻¹) =
        (diagConj (b n0) (P.1⁻¹ * x * P.1), diagConj (b n1) (P.2.1⁻¹ * x * P.2.1),
          diagConj (b n3) (P.2.2⁻¹ * x * P.2.2)) *
        (P.1⁻¹ * x * P.1, P.2.1⁻¹ * x * P.2.1, P.2.2⁻¹ * x * P.2.2)⁻¹ from rfl,
      map_mul, map_inv, h1, mul_inv_cancel]
  obtain ⟨u0, u1, u3, -⟩ := outerTriple_ker (key _ hu)
  obtain ⟨v0, v1, v3, -⟩ := outerTriple_ker (key _ hv)
  have hb0 := eq_one_of_diagConj_sign P.1 u0 v0
  have hb1 := eq_one_of_diagConj_sign P.2.1 u1 v1
  have hb3 := eq_one_of_diagConj_sign P.2.2 u3 v3
  funext j
  fin_cases j
  · exact hb0
  · exact hb1
  · simp
  · exact hb3

theorem rootDiagUnit_mulSingle_mem_thetaPair (t : Lˣ) :
    rootDiagUnit TwistTag.D4.tag (Pi.mulSingle n2 t) ∈ thetaPair L := by
  rw [← thetaHom_HSL]
  exact thetaHom_mem_thetaPair _

end Torus

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
