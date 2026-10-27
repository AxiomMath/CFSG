module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS116Proof

open Matrix
open scoped MatrixGroups
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply)

section Transport

variable (F : Type) [Field F]

theorem projSL_eq_range :
    projSL 2 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

@[expose] noncomputable def toProjSL : SL(2, F) →* projSL 2 F :=
  (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* ProjGenLinGroup (Fin 2) F).codRestrict
    (projSL 2 F) (fun A => by rw [projSL_eq_range]; exact ⟨A, rfl⟩)

theorem toProjSL_surjective : Function.Surjective (toProjSL F) := by
  rintro ⟨x, hx⟩
  rw [projSL_eq_range] at hx
  obtain ⟨A, rfl⟩ := hx
  exact ⟨A, rfl⟩

variable [CharP F 2]

theorem toProjSL_injective : Function.Injective (toProjSL F) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  have h : A ∈ (Matrix.SpecialLinearGroup.toPGL :
      SL(2, F) →* ProjGenLinGroup (Fin 2) F).ker := by
    rw [MonoidHom.mem_ker] at hA ⊢
    exact congrArg Subtype.val hA
  rw [Matrix.SpecialLinearGroup.toPGL_ker,
    CFSG.RankThree.PartOne.KCRootAxis.sl2_center_eq_bot] at h
  exact h

@[expose] noncomputable def projSLEquiv : SL(2, F) ≃* projSL 2 F :=
  MulEquiv.ofBijective (toProjSL F) ⟨toProjSL_injective F, toProjSL_surjective F⟩

theorem exists_conj_slFieldAut [Finite F] (φ : MulAut (projSL 2 F)) :
    ∃ (M : SL(2, F)) (σ : F ≃+* F), ∀ A : SL(2, F),
      φ (projSLEquiv F A) = projSLEquiv F (M * slFieldAut F σ A * M⁻¹) := by
  obtain ⟨M, σ, h⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_conj_mul_slFieldAut
    (MulAut.congr (projSLEquiv F).symm φ)
  refine ⟨M, σ, fun A => ?_⟩
  have h1 := congrArg (fun ψ : MulAut SL(2, F) => projSLEquiv F (ψ A)) h
  simp only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply, MulAut.mul_apply, MulAut.conj_apply] at h1
  exact h1

end Transport

section Matrices

variable {F : Type} [Field F] [CharP F 2]

theorem ofNat_eq_mod_two (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : F) = ((n % 2 : ℕ) : F) := by
  rw [← Nat.cast_ofNat (R := F) (n := n), CharP.cast_eq_mod F 2]
  rfl

omit [CharP F 2] in
theorem coe_eta (M : SL(2, F)) :
    (M : Matrix (Fin 2) (Fin 2) F) = !![M 0 0, M 0 1; M 1 0, M 1 1] :=
  Matrix.eta_fin_two _

theorem eq_one_of_sq_eq_one {x : F} (h : x ^ 2 = 1) : x = 1 :=
  CharTwo.sq_inj.mp (h.trans (one_pow 2).symm)

theorem coe_inv_sl (A : SL(2, F)) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![A 1 1, A 0 1; A 1 0, A 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, CharTwo.neg_eq, CharTwo.neg_eq]

theorem det_entries (A : SL(2, F)) : A 0 0 * A 1 1 + A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rw [det_fin_two, CharTwo.sub_eq_add] at h
  exact h

theorem mul_self_eq (A : SL(2, F)) :
    (A : Matrix (Fin 2) (Fin 2) F) * A =
      (A 0 0 + A 1 1) • (A : Matrix (Fin 2) (Fin 2) F) + 1 := by
  have hd := det_entries A
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | ring1
    | (linear_combination (norm := ring_nf) hd; simp [CharTwo.two_eq_zero])

theorem mul_self_eq_one_of_trace (A : SL(2, F)) (h : A 0 0 + A 1 1 = 0) : A * A = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, mul_self_eq, h, zero_smul, zero_add,
    Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_eq (A : SL(2, F)) :
    ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (A 0 0 + A 1 1) • 1 + (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [coe_inv_sl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

theorem trace_inv_mul (A B : SL(2, F)) :
    (A⁻¹ * B : SL(2, F)) 0 0 + (A⁻¹ * B : SL(2, F)) 1 1 =
      A 1 1 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 0 0 * B 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem det_add (A B : SL(2, F)) :
    ((A : Matrix (Fin 2) (Fin 2) F) + B).det =
      (A⁻¹ * B : SL(2, F)) 0 0 + (A⁻¹ * B : SL(2, F)) 1 1 := by
  rw [trace_inv_mul, det_fin_two]
  have hA := det_entries A
  have hB := det_entries B
  simp only [Matrix.add_apply]
  linear_combination (norm := ring_nf) hA + hB
  simp [CharTwo.two_eq_zero]

theorem matrix_add_self (X : Matrix (Fin 2) (Fin 2) F) : X + X = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem add_mul_add_inv_eq_zero (A B : SL(2, F)) (hAB : A * B = B * A)
    (htr : A 0 0 + A 1 1 = B 0 0 + B 1 1) :
    ((A : Matrix (Fin 2) (Fin 2) F) + B) *
      ((B : Matrix (Fin 2) (Fin 2) F) + ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) = 0 := by
  have hAB' : (A : Matrix (Fin 2) (Fin 2) F) * B = B * A := by
    have := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hAB
    simpa using this
  have hinv : (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hB2 := mul_self_eq B
  rw [← htr] at hB2
  rw [add_mul, mul_add, mul_add, hinv, hB2, coe_inv_eq, mul_add, mul_smul_comm, mul_one,
    ← hAB']
  set t := A 0 0 + A 1 1
  calc (A : Matrix (Fin 2) (Fin 2) F) * B + 1 +
        (t • (B : Matrix (Fin 2) (Fin 2) F) + 1 +
          (t • (B : Matrix (Fin 2) (Fin 2) F) + (A : Matrix (Fin 2) (Fin 2) F) * B))
      = ((A : Matrix (Fin 2) (Fin 2) F) * B + (A : Matrix (Fin 2) (Fin 2) F) * B) + (1 + 1) +
          (t • (B : Matrix (Fin 2) (Fin 2) F) + t • (B : Matrix (Fin 2) (Fin 2) F)) := by abel
    _ = 0 := by simp only [matrix_add_self, add_zero]

omit [CharP F 2] in
theorem trace_conj (M X : SL(2, F)) :
    (M * X * M⁻¹ : SL(2, F)) 0 0 + (M * X * M⁻¹ : SL(2, F)) 1 1 = X 0 0 + X 1 1 := by
  have h1 : ((M * X * M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (M : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) *
        ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
  have h2 : ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h := Matrix.trace_mul_comm
    ((M : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F))
    ((M⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
  rw [← Matrix.mul_assoc, h2, Matrix.one_mul, ← h1, trace_fin_two, trace_fin_two] at h
  exact h

omit [CharP F 2] in
theorem trace_slFieldAut (σ : F ≃+* F) (A : SL(2, F)) :
    (slFieldAut F σ A) 0 0 + (slFieldAut F σ A) 1 1 = σ (A 0 0 + A 1 1) := by
  rw [slFieldAut_apply, slFieldAut_apply, map_add]

end Matrices

end CFSG.RankThree.PartTwo.KFacts.KS116Proof
