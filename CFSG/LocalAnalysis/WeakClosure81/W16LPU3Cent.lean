module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Model
public import CFSG.RankThree.PartTwo.KFacts.K71SU3Torus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.CGT.PushingUpLit.CGT6
open scoped MatrixGroups

variable {s : ℕ} {F : Type} [Field F] (h : UnitaryFieldData 2 s F)

theorem w16l_eq_diagG_of_commute_Sig01 (hs : 2 ≤ s) {g : unitarySU 2 s F 3}
    (hg : ∀ σ ∈ Sig01 h, g * σ = σ * g) :
    ∃ (u w : F) (hu : NO h u) (hw : NO h w) (hdet : u * u * w = 1),
      g = diagG h u u w hu hu hw hdet := by
  set M : Matrix (Fin 3) (Fin 3) F := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hMdef
  obtain ⟨κ, hκ, -, hκ6⟩ := exists_kappa h hs
  have hκ1 : κ ≠ 1 := fun h => hκ6 (by rw [h, one_pow])
  have hκ2ne : κ ^ 2 ≠ 1 := by
    intro h
    apply hκ6
    calc κ ^ 6 = (κ ^ 2) ^ 3 := by rw [← pow_mul]
      _ = 1 := by rw [h, one_pow]
  have hκ_ne_inv : κ ≠ κ⁻¹ := by
    intro heq
    apply hκ2ne
    rw [pow_two]
    exact (show κ * κ = 1 from by simpa [← heq] using mul_inv_cancel₀ hκ.ne_zero)
  have hκinv1 : κ⁻¹ ≠ 1 := fun h => hκ1 (inv_eq_one.mp h)
  have ha : ∀ i j : Fin 3, i ≠ j → (![κ, κ⁻¹, 1] : Fin 3 → F) i ≠ ![κ, κ⁻¹, 1] j :=
    CFSG.RankThree.PartTwo.KFacts.vec3_injective hκ_ne_inv hκ1 hκinv1
  have h1 : NO h (1 : F) := by simp [NO]
  have hdetD : κ * κ⁻¹ * 1 = 1 := by rw [mul_inv_cancel₀ hκ.ne_zero, mul_one]
  have hD : diagG h κ κ⁻¹ 1 hκ hκ.inv h1 hdetD ∈ Sig01 h :=
    diagG_mem_Sig01 h κ κ⁻¹ hκ hκ.inv (mul_inv_cancel₀ hκ.ne_zero) hdetD h1
  have hcommD : M * Matrix.diagonal ![κ, κ⁻¹, 1] = Matrix.diagonal ![κ, κ⁻¹, 1] * M := by
    have h := congrArg (fun x : unitarySU 2 s F 3 =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hg _ hD)
    simpa [hMdef, Subgroup.coe_mul, Units.val_mul, coe_diagG] using h
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := fun i j hij =>
    CFSG.RankThree.PartTwo.KFacts.offDiag_eq_zero_of_commute_diagonal ha hcommD hij
  have hc1 : (1 : F) + h.bar 1 = 0 := by
    rw [map_one]
    exact add_self_eq_zero_of_h h 1
  have hT : tvG h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) 1 hc1 ∈ Sig01 h :=
    tvG_mem_Sig01 h (a₀ : Fin 3 → F) (sqNorm3_a₀ h) 1 hc1 (by simp [a₀])
  have hcommT : M * tvM h (a₀ : Fin 3 → F) 1 = tvM h (a₀ : Fin 3 → F) 1 * M := by
    have h := congrArg (fun x : unitarySU 2 s F 3 =>
      ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) (hg _ hT)
    simpa [hMdef, Subgroup.coe_mul, Units.val_mul, coe_tvG] using h
  have h01 : M 0 0 = M 1 1 := by
    have e := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X 0 1) hcommT
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_three] at e
    rw [hoff 0 1 (by decide), hoff 0 2 (by decide), hoff 2 1 (by decide)] at e
    simpa [tvM_apply, a₀] using e
  have hMfull : M = Matrix.diagonal ![M 0 0, M 0 0, M 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, h01, hoff]
  have hunit : (M.map h.bar)ᵀ * M = 1 := by
    have h := ((mem_unitarySU_iff h).mp g.2).2
    simpa [hMdef] using h
  have hunit' : Matrix.diagonal
      (fun i => h.bar (![M 0 0, M 0 0, M 2 2] i) * ![M 0 0, M 0 0, M 2 2] i) = 1 := by
    rw [hMfull, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hunit
    exact hunit
  have hu : NO h (M 0 0) := by
    have h := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X 0 0) hunit'
    simpa [NO, Matrix.diagonal_apply] using h
  have hw : NO h (M 2 2) := by
    have h := congrArg (fun X : Matrix (Fin 3) (Fin 3) F => X 2 2) hunit'
    simpa [NO, Matrix.diagonal_apply] using h
  have hdetM : M.det = 1 := by
    have h := ((mem_unitarySU_iff h).mp g.2).1
    simpa [hMdef] using h
  have hdet : M 0 0 * M 0 0 * M 2 2 = 1 := by
    rw [hMfull, Matrix.det_diagonal, Fin.prod_univ_three] at hdetM
    simpa using hdetM
  refine ⟨M 0 0, M 2 2, hu, hw, hdet, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_diagG, ← hMdef]
  exact hMfull

theorem w16l_diagG_mem_unitaryScalars_iff (u w : F) (hu : NO h u) (hw : NO h w)
    (hdet : u * u * w = 1) :
    diagG h u u w hu hu hw hdet ∈ unitaryScalars h 3 ↔ u ^ 3 = 1 := by
  constructor
  · intro hmem
    obtain ⟨c, -, hc3, hscalar⟩ := mem_unitaryScalars.mp hmem
    have e00 : u = (c : F) := by
      have hmat :=
        congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F)) 0 0) hscalar
      simpa [coe_diagG, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using hmat
    rw [e00, ← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  · intro hu3
    have hw_eq : w = u := by
      have h2 : u * u ≠ 0 := mul_ne_zero hu.ne_zero hu.ne_zero
      apply mul_left_cancel₀ h2
      calc u * u * w = 1 := hdet
        _ = u ^ 3 := hu3.symm
        _ = u * u * u := by ring
    have hnorm : h.norm ((Units.mk0 u hu.ne_zero : Fˣ) : F) = 1 := by
      show u * h.bar u = 1
      rw [mul_comm]
      exact hu
    have hc3 : (Units.mk0 u hu.ne_zero : Fˣ) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      simpa using hu3
    refine mem_unitaryScalars.mpr ⟨Units.mk0 u hu.ne_zero, hnorm, hc3, ?_⟩
    apply Units.ext
    rw [coe_diagG, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hw_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end CFSG.LocalAnalysis.WeakClosure81

end
