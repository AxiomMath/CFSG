module

public import CFSG.Quasithin.Vol2.Ch11SecS12O

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

@[expose] def invGL (M : Matrix (Fin 3) (Fin 3) F) (h : M * M = 1) : GL (Fin 3) F :=
  ⟨M, M, h, h⟩

omit [CharP F 2] in
theorem invGL_coe (M : Matrix (Fin 3) (Fin 3) F) (h : M * M = 1) :
    ((invGL M h : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := rfl

omit [CharP F 2] in
theorem invGL_inv_coe (M : Matrix (Fin 3) (Fin 3) F) (h : M * M = 1) :
    (((invGL M h)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M := rfl

theorem add_ne_zero_of_ne {a d : F} (h : a ≠ d) : a + d ≠ 0 := by
  intro h0
  apply h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h0 - d * h2

theorem exists_conj_diag_zero {g : GL (Fin 3) F} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h11 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2)
    (had : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ (g : Matrix (Fin 3) (Fin 3) F) 1 1) :
    ∃ m : GL (Fin 3) F, ((m * g * m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(g : Matrix (Fin 3) (Fin 3) F) 0 0, (g : Matrix (Fin 3) (Fin 3) F) 1 1,
        (g : Matrix (Fin 3) (Fin 3) F) 1 1] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc := add_ne_zero_of_ne had
  obtain ⟨s, hs⟩ : ∃ s : F, s * ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
      (g : Matrix (Fin 3) (Fin 3) F) 1 1) = (g : Matrix (Fin 3) (Fin 3) F) 0 1 :=
    ⟨_, div_mul_cancel₀ _ hc⟩
  obtain ⟨t, ht⟩ : ∃ t : F, t * ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
      (g : Matrix (Fin 3) (Fin 3) F) 1 1) = (g : Matrix (Fin 3) (Fin 3) F) 0 2 :=
    ⟨_, div_mul_cancel₀ _ hc⟩
  have hM : (!![1, s, t; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
      !![1, s, t; 0, 1, 0; 0, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp
    · linear_combination s * h2
    · linear_combination t * h2
  refine ⟨invGL _ hM, ?_⟩
  rw [Units.val_mul, Units.val_mul, invGL_coe, invGL_inv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [h10, h20, h12, h21]
  · linear_combination hs + (g : Matrix (Fin 3) (Fin 3) F) 0 1 * h2
  · linear_combination ht - t * h11 + (g : Matrix (Fin 3) (Fin 3) F) 0 2 * h2
  · exact h11.symm

theorem exists_conj_diag_one {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1)
    (had : (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ (g : Matrix (Fin 3) (Fin 3) F) 0 0) :
    ∃ m : GL (Fin 3) F, ((m * g * m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(g : Matrix (Fin 3) (Fin 3) F) 2 2, (g : Matrix (Fin 3) (Fin 3) F) 0 0,
        (g : Matrix (Fin 3) (Fin 3) F) 0 0] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc := add_ne_zero_of_ne had
  obtain ⟨s, hs⟩ : ∃ s : F, s * ((g : Matrix (Fin 3) (Fin 3) F) 2 2 +
      (g : Matrix (Fin 3) (Fin 3) F) 0 0) = (g : Matrix (Fin 3) (Fin 3) F) 0 2 :=
    ⟨_, div_mul_cancel₀ _ hc⟩
  obtain ⟨t, ht⟩ : ∃ t : F, t * ((g : Matrix (Fin 3) (Fin 3) F) 2 2 +
      (g : Matrix (Fin 3) (Fin 3) F) 0 0) = (g : Matrix (Fin 3) (Fin 3) F) 1 2 :=
    ⟨_, div_mul_cancel₀ _ hc⟩
  have hM₁ : (!![0, 0, 1; 0, 1, t; 1, 0, s] : Matrix (Fin 3) (Fin 3) F) *
      !![s, 0, 1; t, 1, 0; 1, 0, 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp
    all_goals linear_combination (exp := 1) _ * h2
  have hM₂ : (!![s, 0, 1; t, 1, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) F) *
      !![0, 0, 1; 0, 1, t; 1, 0, s] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp
    all_goals linear_combination (exp := 1) _ * h2
  refine ⟨⟨_, _, hM₁, hM₂⟩, ?_⟩
  rw [Units.val_mul, Units.val_mul]
  show !![0, 0, 1; 0, 1, t; 1, 0, s] * (g : Matrix (Fin 3) (Fin 3) F) *
    !![s, 0, 1; t, 1, 0; 1, 0, 0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [h20, h21, h01, h10]
  all_goals first
    | exact h00.symm
    | linear_combination ht + (g : Matrix (Fin 3) (Fin 3) F) 1 2 * h2 - t * h00
    | linear_combination hs + (g : Matrix (Fin 3) (Fin 3) F) 0 2 * h2

omit [CharP F 2] in
theorem block_of_commute {g h : GL (Fin 3) F} {a d : F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, d, d]) (had : a ≠ d)
    (hc : ProjGenLinGroup.mk h * ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk h) :
    (h : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (h : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
      (h : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  have hdetg : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [hg, Matrix.det_fin_three] at hdetg
  simp at hdetg
  obtain ⟨ha0, hd0⟩ := hdetg
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at hc
  obtain ⟨c, hc⟩ := hc
  have hm := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at hm
  rw [hg] at hm
  have e : ∀ i j, (h : Matrix (Fin 3) (Fin 3) F) i j * ![a, d, d] j * (c : F) =
      ![a, d, d] i * (h : Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
    have := congrFun (congrFun hm i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.scalar_apply] using this
  have hda : d - a ≠ 0 := sub_ne_zero.mpr (Ne.symm had)
  by_cases hc1 : (c : F) = 1
  · have e01 := e 0 1
    have e02 := e 0 2
    have e10 := e 1 0
    have e20 := e 2 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, hc1, mul_one] at e01 e02 e10 e20
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : (h : Matrix (Fin 3) (Fin 3) F) 0 1 * (d - a) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hda
    · have : (h : Matrix (Fin 3) (Fin 3) F) 0 2 * (d - a) = 0 := by linear_combination e02
      exact (mul_eq_zero.mp this).resolve_right hda
    · have : (h : Matrix (Fin 3) (Fin 3) F) 1 0 * (d - a) = 0 := by linear_combination -e10
      exact (mul_eq_zero.mp this).resolve_right hda
    · have : (h : Matrix (Fin 3) (Fin 3) F) 2 0 * (d - a) = 0 := by linear_combination -e20
      exact (mul_eq_zero.mp this).resolve_right hda
  · exfalso
    have hc1' : (c : F) - 1 ≠ 0 := sub_ne_zero.mpr hc1
    have z : ∀ i j : Fin 3, ![a, d, d] j = ![a, d, d] i →
        (h : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
      intro i j hij
      have hx : ![a, d, d] i ≠ 0 := by
        fin_cases i <;> simp [ha0, hd0]
      have := e i j
      rw [hij] at this
      have h2 : (h : Matrix (Fin 3) (Fin 3) F) i j * ![a, d, d] i * ((c : F) - 1) = 0 := by
        linear_combination this
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact (mul_eq_zero.mp h3).resolve_right hx
      · exact absurd h3 hc1'
    have hdeth : (h : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    apply hdeth
    rw [Matrix.det_fin_three, z 0 0 rfl, z 1 1 rfl, z 2 2 rfl, z 1 2 rfl, z 2 1 rfl]
    ring

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
