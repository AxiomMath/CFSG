module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {F : Type*} [Field F]

@[expose] def IsUnitri (g : Matrix.SpecialLinearGroup (Fin 3) F) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1

theorem isUnitri_mul {g h : Matrix.SpecialLinearGroup (Fin 3) F} (hg : IsUnitri g)
    (hh : IsUnitri h) : IsUnitri (g * h) := by
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := hg
  obtain ⟨h10, h20, h21, h00, h11, h22⟩ := hh
  simp [IsUnitri, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    g10, g20, g21, g00, g11, g22, h10, h20, h21, h00, h11, h22]

theorem isUnitri_inv {g : Matrix.SpecialLinearGroup (Fin 3) F} (hg : IsUnitri g) :
    IsUnitri g⁻¹ := by
  obtain ⟨g10, g20, g21, g00, g11, g22⟩ := hg
  simp [IsUnitri, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three,
    g10, g20, g21, g00, g11, g22]

theorem isUnitri_one : IsUnitri (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
  simp [IsUnitri]

@[expose] def unitriMat (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, c; 0, 1, b; 0, 0, 1]

theorem det_unitriMat (a b c : F) : (unitriMat a b c).det = 1 := by
  simp [unitriMat, Matrix.det_fin_three]

@[expose] def unitriMk (a b c : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨unitriMat a b c, det_unitriMat a b c⟩

theorem isUnitri_mk (a b c : F) : IsUnitri (unitriMk a b c) := by
  simp [IsUnitri, unitriMk, unitriMat]

@[expose] def unitriSL : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) where
  carrier := {g | IsUnitri g}
  mul_mem' := fun {_ _} hg hh => isUnitri_mul hg hh
  one_mem' := isUnitri_one
  inv_mem' := fun {_} hg => isUnitri_inv hg

def unitriEquiv : F × F × F ≃ unitriSL (F := F) where
  toFun p := ⟨unitriMk p.1 p.2.1 p.2.2, isUnitri_mk _ _ _⟩
  invFun u :=
    (((u : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1,
      ((u : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2,
      ((u : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2)
  left_inv p := by
    simp [unitriMk, unitriMat]
  right_inv u := by
    have hu : IsUnitri (u : Matrix.SpecialLinearGroup (Fin 3) F) := u.2
    obtain ⟨g10, g20, g21, g00, g11, g22⟩ := hu
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [unitriMk, unitriMat, g10, g20, g21, g00, g11, g22]

theorem card_unitriSL [Fintype F] : Nat.card (unitriSL (F := F)) = Fintype.card F ^ 3 := by
  rw [← Nat.card_congr unitriEquiv, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card]
  ring

theorem prod_card_identity (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1))) := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : q ^ 2 ≤ q ^ 3 := by nlinarith
  have h3 : q ≤ q ^ 3 := by nlinarith
  have h4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h5 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  zify [h1, h2, h3, h4, h5, hq]
  ring

theorem card_SL3 [Fintype F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Fintype.card F ^ 3 * ((Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 2 - 1)) := by
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hprod : ∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) =
      (Fintype.card F - 1) *
        (Fintype.card F ^ 3 * ((Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 2 - 1))) := by
    simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    exact prod_card_identity _ hq
  rw [Matrix.card_SL_field 3, hprod, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt hq1)]

theorem index_unitriSL [Fintype F] :
    (unitriSL (F := F)).index = (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 2 - 1) := by
  have h := Subgroup.index_mul_card (H := unitriSL (F := F))
  rw [card_unitriSL, card_SL3] at h
  have hpos : 0 < Fintype.card F ^ 3 := pow_pos Fintype.card_pos 3
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [mul_comm, h]

theorem odd_index_unitriSL [Fintype F] [CharP F 2] :
    Odd (unitriSL (F := F)).index := by
  rw [index_unitriSL]
  have hq2 : Fintype.card F % 2 = 0 :=
    FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hodd3 : Odd (Fintype.card F ^ 3 - 1) := by
    have hev : Fintype.card F ^ 3 % 2 = 0 := by simp [Nat.pow_mod, hq2]
    have hpos : 1 ≤ Fintype.card F ^ 3 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.odd_iff]
    generalize Fintype.card F ^ 3 = t at hev hpos ⊢
    omega
  have hodd2 : Odd (Fintype.card F ^ 2 - 1) := by
    have hev : Fintype.card F ^ 2 % 2 = 0 := by simp [Nat.pow_mod, hq2]
    have hpos : 1 ≤ Fintype.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.odd_iff]
    generalize Fintype.card F ^ 2 = t at hev hpos ⊢
    omega
  exact hodd3.mul hodd2

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
