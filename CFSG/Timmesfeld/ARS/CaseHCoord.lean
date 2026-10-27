module

public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal Matrix

variable {G : Type*} [Group G]

namespace CaseH

section SL3

variable {F : Type*} [Field F]

@[expose] noncomputable def diag3 (l : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![(l : F), 1, ((l⁻¹ : Fˣ) : F)], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem val_mul3 (x y : SpecialLinearGroup (Fin 3) F) : (x * y).1 = x.1 * y.1 := rfl

theorem val_tv {i j : Fin 3} (h : i ≠ j) (b : F) :
    (SpecialLinearGroup.transvection h b).1 = 1 + Matrix.single i j b :=
  SpecialLinearGroup.transvection_coe h b

theorem diag3_mul_tv01 (l : Fˣ) (u : F) :
    diag3 l * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) u =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) ((l : F) * u) *
        diag3 l := by
  apply Subtype.ext
  rw [val_mul3, val_mul3, val_tv, val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem diag3_conj_tv01 (l : Fˣ) (u : F) :
    diag3 l * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) u * (diag3 l)⁻¹ =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) ((l : F) * u) := by
  rw [diag3_mul_tv01, mul_inv_cancel_right]

theorem diag3_mul (l l' : Fˣ) : diag3 l * diag3 l' = (diag3 (l * l') : SpecialLinearGroup (Fin 3) F) := by
  apply Subtype.ext
  rw [val_mul3]
  simp only [diag3, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem diag3_eq [CharP F 2] (l : Fˣ) :
    diag3 l = SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (l : F) *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) ((l⁻¹ : Fˣ) : F) *
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (l : F) *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) 1 *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) 1 *
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : F) = 1 := by
    rw [show (3 : F) = 2 + 1 by norm_num, h2, zero_add]
  have h4 : (4 : F) = 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : F) = 0 := by
    rw [show (6 : F) = 2 * 3 by norm_num, h2, zero_mul]
  apply Subtype.ext
  simp only [val_mul3, val_tv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply] <;>
    ring_nf <;> simp [h2, h3, h4, h6]

end SL3

section Coord

variable {F : Type} [Field F] {P A A₀ : Subgroup G}
  {ψ : SpecialLinearGroup (Fin (2 + 1)) F →* G}

theorem psi_tv_mem {i j : Fin 3} (hij : i ≠ j) {X : Subgroup G}
    (hX : (SpecialLinear.rootSubgroup 2 F hij).map ψ = X) (u : F) :
    ψ (SpecialLinearGroup.transvection hij u) ∈ X := by
  rw [← hX]
  exact Subgroup.mem_map_of_mem ψ (SpecialLinear.transvection_mem_rootSubgroup hij u)

theorem exists_psi_tv_eq {i j : Fin 3} (hij : i ≠ j) {X : Subgroup G}
    (hX : (SpecialLinear.rootSubgroup 2 F hij).map ψ = X) {x : G} (hx : x ∈ X) :
    ∃ u, ψ (SpecialLinearGroup.transvection hij u) = x := by
  rw [← hX] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨u, rfl⟩ := (SpecialLinear.mem_rootSubgroup hij g).1 hg
  exact ⟨u, rfl⟩

theorem psi_diag3_mem [CharP F 2]
    (hA : (SpecialLinear.rootSubgroup 2 F (show (0 : Fin 3) ≠ 2 by decide)).map ψ = A)
    (hA₀ : (SpecialLinear.rootSubgroup 2 F (show (2 : Fin 3) ≠ 0 by decide)).map ψ = A₀)
    (l : Fˣ) : ψ (diag3 l) ∈ A ⊔ A₀ := by
  rw [diag3_eq]
  simp only [map_mul]
  have ha := fun u => Subgroup.mem_sup_left (S := A) (T := A₀) (psi_tv_mem _ hA u)
  have hb := fun u => Subgroup.mem_sup_right (S := A) (T := A₀) (psi_tv_mem _ hA₀ u)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ha _) (hb _)) (ha _))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (ha _) (hb _)) (ha _))

end Coord

end CaseH

end CFSG.Timmesfeld.ARS
