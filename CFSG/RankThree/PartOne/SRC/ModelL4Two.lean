module

public import CFSG.RankThree.PartOne.SRC.ModelL4
public import CFSG.RankThree.PartOne.SRC.ProductCover

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix

section Diag4

variable {F : Type*} [Field F]

@[expose] def diagMat4 (A B : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

theorem diagMat4_mul (A B A' B' : Matrix (Fin 2) (Fin 2) F) :
    diagMat4 (A * A') (B * B') = diagMat4 A B * diagMat4 A' B' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagMat4, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem diagMat4_one : diagMat4 (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat4]

theorem det_diagMat4 (A B : Matrix (Fin 2) (Fin 2) F) :
    (diagMat4 A B).det = A.det * B.det := by
  rw [Matrix.det_fin_two A, Matrix.det_fin_two B]
  simp [diagMat4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def diagSL4 (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup (Fin 4) F :=
  ⟨diagMat4 (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F), by
    rw [det_diagMat4, x.1.2, x.2.2, mul_one]⟩

theorem coe_diagSL4 (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((diagSL4 x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagMat4 (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] def diagHom4 :
    SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 4) F
    where
  toFun := diagSL4
  map_one' := by
    ext i j
    rw [coe_diagSL4]
    fin_cases i <;> fin_cases j <;> simp [diagMat4]
  map_mul' x y := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL4, coe_diagSL4, coe_diagSL4]
    fin_cases i <;> fin_cases j <;>
      simp [diagMat4, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]

theorem coe_diagHom4 (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((diagHom4 x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagMat4 (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) := rfl

theorem diagHom4_comm_invol4 (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    diagHom4 x * invol4 = invol4 * diagHom4 x := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_diagHom4,
    coe_invol4]
  fin_cases i <;> fin_cases j <;> simp [diagMat4, Matrix.mul_apply, Fin.sum_univ_four]

theorem sq_eq_one_of_diagHom4_mem_center
    {x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F}
    (h : diagHom4 x ∈ Subgroup.center (SpecialLinearGroup (Fin 4) F)) : x ^ 2 = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have e := fun i j => congrFun (congrFun hr i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e23 := e 2 3
  have e32 := e 3 2
  have e33 := e 3 3
  simp [coe_diagHom4, diagMat4, Matrix.scalar_apply] at e00 e01 e10 e11 e22 e23 e32 e33
  have d1 := x.1.2
  have d2 := x.2.2
  rw [Matrix.det_fin_two] at d1 d2
  have hrr1 : r * r = 1 := by
    rw [← e00, ← e11, ← e01, ← e10] at d1
    linear_combination d1
  have hrr2 : r * r = 1 := by
    rw [← e22, ← e33, ← e23, ← e32] at d2
    linear_combination d2
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · ext i j
    show ((x.1 ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = _
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← e00, ← e01, ← e10, ← e11, hrr1]
  · ext i j
    show ((x.2 ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = _
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← e22, ← e23, ← e32, ← e33, hrr2]

end Diag4


theorem rankFourCover_psl4_two {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]
    (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 2 ≤ e) (h9 : Nat.card F ≠ 9) :
    RankFourCover p (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) := by
  have hneg : (-1 : F) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq F p]; exact hp2)
  refine rankFourCover_of_cover_ker (Fact.out : p.Prime) hp2
    (fun _ _ _ ρ hρ hk => rank_four_of_cover_SL2_prod hF hF hp2 he he h9 h9 ρ hρ hk)
    ((QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) F))).comp diagHom4)
    ?_ (orderOf_psl4Invol hneg) ?_
  · intro x hx
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact sq_eq_one_of_diagHom4_mem_center hx
  · intro x
    rw [MonoidHom.comp_apply, psl4Invol, ← map_mul, ← map_mul, diagHom4_comm_invol4]

end CFSG.RankThree.PartOne.SRC
