module

public import CFSG.Quasithin.Background.HSL3S77Model
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin.H.S77

open Matrix

@[expose] def stabE1 : Subgroup SL32 where
  carrier := {g | act g e1 = e1}
  mul_mem' := fun {g h} hg hh => by
    change ((g * h : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    rw [show (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1 from hh]
    exact hg
  one_mem' := by
    change ((1 : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  inv_mem' := fun {g} hg => by
    change ((g⁻¹ : SL32) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1
    have hg' : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ e1 = e1 := hg
    conv_lhs => rw [← hg']
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def blk (g : SL32) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i.succ j.succ

theorem col_zero {g : SL32} (hg : act g e1 = e1) (i : Fin 2) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i.succ 0 = 0 := by
  have h := congrFun hg i.succ
  rw [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h
  fin_cases i <;> simpa using h

theorem blk_mul {g h : SL32} (hg : act g e1 = e1) : blk (g * h) = blk g * blk h := by
  ext i j
  rw [blk, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_succ, col_zero hg,
    zero_mul, zero_add, Matrix.mul_apply]
  rfl

theorem blk_one : blk 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def blkHom : stabE1 →* GL (Fin 2) (ZMod 2) :=
  MonoidHom.toHomUnits
    { toFun := fun g => blk g
      map_one' := blk_one
      map_mul' := fun g _ => blk_mul g.2 }

theorem coe_blkHom (g : stabE1) : (blkHom g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = blk g := rfl

theorem card_GL2 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  have h2 : (∏ i : Fin 2, (Fintype.card (ZMod 2) ^ 2 - Fintype.card (ZMod 2) ^ (i : ℕ))) = 6 := by
    rw [Fin.prod_univ_two, ZMod.card]
    norm_num
  exact (Matrix.card_GL_field (𝔽 := ZMod 2) 2).trans h2

theorem entries_of_blk {g : SL32} (hg : act g e1 = e1) (hb : blk g = 1) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1 := by
  have h0 := congrFun hg 0
  simp only [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0
  have hb' := fun i j => congrFun (congrFun hb i) j
  refine ⟨?_, col_zero hg 0, col_zero hg 1, ?_, ?_, ?_, ?_⟩
  · simpa using h0
  · simpa [blk] using hb' 0 0
  · simpa [blk] using hb' 0 1
  · simpa [blk] using hb' 1 0
  · simpa [blk] using hb' 1 1

theorem blk_fix_H1 {g : SL32} (hg : act g e1 = e1) (hb : blk g = 1) :
    (∀ x : Vec, x 0 = 0 → act g x + x = 0 ∨ act g x + x = e1) ∧
      ∀ y : Vec, y 0 = 0 → (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ y = y := by
  obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := entries_of_blk hg hb
  have h2 : ∀ c : ZMod 2, c + c = 0 := by decide
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1 * x 1 +
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2 * x 2) with h | h
    · left
      funext i
      fin_cases i
      · simpa [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx, h00] using h
      all_goals simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx, h10, h20, h11, h12,
        h21, h22, h2]
    · right
      funext i
      fin_cases i
      · simpa [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx, h00] using h
      all_goals simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hx, h10, h20, h11, h12,
        h21, h22, h2]
  · funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply, hy, h10, h20,
        h11, h12, h21, h22]

theorem blk_fix_H0 {g : SL32} (hg : act g e1 = e1)
    (hd : (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ e1 = e1) (hb : blk g = 1) : g = 1 := by
  obtain ⟨h00, h10, h20, h11, h12, h21, h22⟩ := entries_of_blk hg hb
  have hd1 := congrFun hd 1
  have hd2 := congrFun hd 2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply] at hd1 hd2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem hyp_fix {g : SL32} (hg : act g e1 = e1) (hx : ∀ x : Vec, x 0 = 0 → act g x = x) :
    g = 1 := by
  have h2 := hx ![0, 1, 0] rfl
  have h3 := hx ![0, 0, 1] rfl
  have h1 := hg
  apply Subtype.ext
  ext i j
  have e1' := congrFun h1 i
  have e2' := congrFun h2 i
  have e3' := congrFun h3 i
  simp only [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1' e2' e3'
  fin_cases i <;> fin_cases j <;> simp_all

theorem dact_zero_of_stab {g : SL32} (hg : act g e1 = e1) {y : Vec} (hy : y 0 = 0) :
    (dact g y) 0 = 0 := by
  have hgi : act g⁻¹ e1 = e1 := stabE1.inv_mem (show g ∈ stabE1 from hg)
  have h0 := congrFun hgi 0
  simp only [act, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0
  have h1 := col_zero hgi 0
  have h2 := col_zero hgi 1
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h2
  simp only [dact, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.transpose_apply, hy, h1,
    h2]
  simp

end CFSG.Quasithin.H.S77
