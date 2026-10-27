module

public import CFSG.Quasithin.Vol2.Ch10SecB3Obl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

variable {F : Type} [Field F]

@[expose] def dU (l : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem coe_dU (l : Fˣ) : ((dU l : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = !![(l : F), 0; 0, ((l⁻¹ : Fˣ) : F)] := rfl

theorem dU_mul (a b : Fˣ) : dU a * dU b = dU (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem dU_one : dU (1 : Fˣ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dU]

theorem dU_inv (a : Fˣ) : (dU a)⁻¹ = dU a⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [dU_mul, mul_inv_cancel, dU_one]

theorem dU_injective : Function.Injective (dU (F := F)) := by
  intro a b h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [coe_dU] at h1
  exact Units.ext (by simpa using h1)

theorem map_dU (σ : F ≃+* F) (l : Fˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (dU l) =
      dU (Units.map σ.toRingHom.toMonoidHom l) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dU]

theorem card_le_four [Finite F] (h2 : (2 : F) = 0)
    (h : ∀ x : F, x ≠ 0 → x ≠ 1 → x ^ 2 + x + 1 = 0) : Nat.card F ≤ 4 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  by_cases hex : ∃ x : F, x ≠ 0 ∧ x ≠ 1
  · obtain ⟨x, hx0, hx1⟩ := hex
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1, x, x + 1} := by
      intro y _
      by_cases hy0 : y = 0
      · simp [hy0]
      by_cases hy1 : y = 1
      · simp [hy1]
      have hx := h x hx0 hx1
      have hy := h y hy0 hy1
      have hprod : (y + x) * (y + x + 1) = 0 := by
        linear_combination hy + hx + (x * y - 1) * h2
      rcases mul_eq_zero.mp hprod with h3 | h3
      · have : y = x := by linear_combination h3 - x * h2
        simp [this]
      · have : y = x + 1 := by linear_combination h3 - (x + 1) * h2
        simp [this]
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1, x, x + 1} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
        simp
  · push Not at hex
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
      intro y _
      by_cases hy0 : y = 0
      · simp [hy0]
      · simp [hex y hy0]
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card hsub
      _ ≤ 4 := (Finset.card_le_two).trans (by norm_num)

theorem diag_or_antidiag [CharP F 2] {g : Matrix.SpecialLinearGroup (Fin 2) F} {μ ν : Fˣ}
    (hμ : (μ : F) ≠ ((μ⁻¹ : Fˣ) : F)) (hg : g * dU μ = dU ν * g) :
    (∃ a : Fˣ, g = dU a) ∨
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 0) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc : ∀ i j, ((g * dU μ : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j = ((dU ν * g : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hg]
  have e00 := hc 0 0
  have e01 := hc 0 1
  have e10 := hc 1 0
  have e11 := hc 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dU, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, zero_mul, add_zero, zero_add]
    at e00 e01 e10 e11
  set a := (g : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (g : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (g : Matrix (Fin 2) (Fin 2) F) 1 0
  set e := (g : Matrix (Fin 2) (Fin 2) F) 1 1
  have hdet : a * e - b * c = 1 := by rw [← Matrix.det_fin_two]; exact g.2
  have hμ' : (μ : F) - ((μ⁻¹ : Fˣ) : F) ≠ 0 := sub_ne_zero.mpr hμ
  by_cases ha : a = 0
  · right
    refine ⟨ha, ?_⟩
    have hbc : b * c = 1 := by linear_combination -hdet + e * ha - h2
    have hb : b ≠ 0 := left_ne_zero_of_mul_eq_one hbc
    have hc0 : c ≠ 0 := right_ne_zero_of_mul_eq_one hbc
    have hν : (ν : F) = ((μ⁻¹ : Fˣ) : F) := by
      have : b * (((μ⁻¹ : Fˣ) : F) - ν) = 0 := by linear_combination e01
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)).symm
    have : e * (((μ⁻¹ : Fˣ) : F) - ((ν⁻¹ : Fˣ) : F)) = 0 := by linear_combination e11
    have hν' : ((ν⁻¹ : Fˣ) : F) = μ := by
      rw [Units.val_inv_eq_inv_val, hν, Units.val_inv_eq_inv_val, inv_inv]
    rw [hν'] at this
    have h3 : ((μ⁻¹ : Fˣ) : F) - μ ≠ 0 := by
      intro h
      exact hμ (sub_eq_zero.mp h).symm
    exact (mul_eq_zero.mp this).resolve_right h3
  · left
    have hν : (ν : F) = μ := by
      have : a * ((μ : F) - ν) = 0 := by linear_combination e00
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)).symm
    have hb : b = 0 := by
      have : b * (((μ⁻¹ : Fˣ) : F) - μ) = 0 := by rw [← hν]; linear_combination e01
      refine (mul_eq_zero.mp this).resolve_right ?_
      intro h
      exact hμ (sub_eq_zero.mp h).symm
    have hc0 : c = 0 := by
      have hν' : ((ν⁻¹ : Fˣ) : F) = ((μ⁻¹ : Fˣ) : F) := by
        rw [Units.val_inv_eq_inv_val, hν, Units.val_inv_eq_inv_val]
      have : c * ((μ : F) - ((μ⁻¹ : Fˣ) : F)) = 0 := by rw [← hν']; linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hμ'
    have hae : a * e = 1 := by rw [hb, zero_mul, sub_zero] at hdet; exact hdet
    refine ⟨Units.mk0 a ha, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [coe_dU, a]
    · simp [coe_dU, b, hb]
    · simp [coe_dU, c, hc0]
    · simp only [coe_dU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.empty_val', Units.val_inv_eq_inv_val, Units.val_mk0]
      exact (eq_inv_of_mul_eq_one_right hae).symm ▸ rfl

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
