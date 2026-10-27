module

public import CFSG.RankThree.GF2n.Smith81.Lin213Outside
public import CFSG.CGT.Timmesfeld75.ListWCLinPair
public import CFSG.RankThree.GF2n.Smith81.S81NTk

open CFSG.RankThree.GF2n.Smith81.A5Cube
open scoped Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type*} [Field K]

private def m1Dot {n : ℕ} (a : Fin n → K) : Module.Dual K (Fin n → K) where
  toFun x := a ⬝ᵥ x
  map_add' x y := dotProduct_add a x y
  map_smul' r x := by simp [dotProduct_smul]

private theorem m1_isTransvection {n : ℕ} {x : Matrix.SpecialLinearGroup (Fin n) K}
    {c a : Fin n → K} (hc : c ≠ 0) (ha : a ≠ 0) (hac : a ⬝ᵥ c = 0)
    (hx : (x : Matrix (Fin n) (Fin n) K) = 1 + Matrix.vecMulVec c a) :
    CFSG.CGT.Timmesfeld75.IsTransvection x := by
  refine ⟨fun h => CFSG.CGT.Timmesfeld75.vecMulVec_ne_zero_of hc ha ?_, m1Dot a, c,
    (show m1Dot a c = 0 from hac), ?_⟩
  · rw [h, Matrix.SpecialLinearGroup.coe_one] at hx
    have := congrArg (fun M => M - 1) hx
    simpa using this.symm
  · refine LinearEquiv.ext fun v => ?_
    rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, hx,
      CFSG.CGT.Timmesfeld75.one_add_vecMulVec_mulVec]
    rfl

private theorem m1_tInv1_coe :
    ((tInv1 K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 + Matrix.vecMulVec (Pi.single 0 1) (Pi.single 1 1) := by
  rw [tInv1, transvGL_val, Matrix.transvection]
  congr 1
  ext p q
  fin_cases p <;> fin_cases q <;> simp [Matrix.vecMulVec, Matrix.single_apply, Pi.single_apply]

theorem exists_conj_tInv1 [Finite K] [CharP K 2] {g : GL (Fin 6) K} (hg : IsTransvec K g) :
    ∃ c : GL (Fin 6) K, (c : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ c * g * c⁻¹ = tInv1 K := by
  obtain ⟨a, f, ha, hf, hfa, hgM⟩ := IsTransvec.exists hg
  have he : (Pi.single 1 1 : Fin 6 → K) ⬝ᵥ (Pi.single 0 1 : Fin 6 → K) = 0 := by
    rw [dotProduct_single]
    simp [Pi.single_apply]
  have he0 : (Pi.single 0 1 : Fin 6 → K) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  have he1 : (Pi.single 1 1 : Fin 6 → K) ≠ 0 := by
    intro h
    simpa using congrFun h 1
  obtain ⟨W, hW⟩ := transv_conj_SL
    (m1_isTransvection (x := CFSG.CGT.Timmesfeld75.tvSL a f hfa) ha hf hfa rfl)
    (m1_isTransvection (x := CFSG.CGT.Timmesfeld75.tvSL (Pi.single 0 1) (Pi.single 1 1) he)
      he0 he1 he rfl)
  have h2 : W * CFSG.CGT.Timmesfeld75.tvSL a f hfa =
      CFSG.CGT.Timmesfeld75.tvSL (Pi.single 0 1) (Pi.single 1 1) he * W := by
    rw [← hW, inv_mul_cancel_right]
  have h3 := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 6) K =>
    (X : Matrix (Fin 6) (Fin 6) K)) h2
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h3
  rw [CFSG.CGT.Timmesfeld75.coe_tvSL, CFSG.CGT.Timmesfeld75.coe_tvSL] at h3
  refine ⟨Matrix.SpecialLinearGroup.toGL W, Matrix.SpecialLinearGroup.det_coe W, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hgM, m1_tInv1_coe]
  exact h3

end CFSG.RankThree.GF2n.Smith81.A5Cube
