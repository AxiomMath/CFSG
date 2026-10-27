module

public import CFSG.Quasithin.Background.H11Defs
public import CFSG.Quasithin.Background.HFL3Exp
public import CFSG.Quasithin.Background.HSU3Defs

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def stabW (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    obtain ⟨hg0, hg1⟩ := hg
    obtain ⟨hh0, hh1⟩ := hh
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
        hh0, hh1]
  inv_mem' {g} hg := by
    obtain ⟨hg0, hg1⟩ := hg
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1]

@[expose] def stabZ (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    obtain ⟨hg0, hg1⟩ := hg
    obtain ⟨hh0, hh1⟩ := hh
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
        hh0, hh1]
  inv_mem' {g} hg := by
    obtain ⟨hg0, hg1⟩ := hg
    refine ⟨?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1]

@[expose] def perfW (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    obtain ⟨hg0, hg1, hg2⟩ := hg
    obtain ⟨hh0, hh1, hh2⟩ := hh
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
        hg2, hh0, hh1, hh2]
  inv_mem' {g} hg := by
    obtain ⟨hg0, hg1, hg2⟩ := hg
    have hdet := g.2
    rw [Matrix.det_fin_three, hg0, hg1, hg2] at hdet
    refine ⟨?_, ?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1, hg2]
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1, hg2]
    · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
      simp [hg0, hg1, hg2]
      linear_combination hdet

@[expose] def perfZ (K : Type) [Field K] : Subgroup SL(3, K) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    obtain ⟨hg0, hg1, hg2⟩ := hg
    obtain ⟨hh0, hh1, hh2⟩ := hh
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1,
        hg2, hh0, hh1, hh2]
  inv_mem' {g} hg := by
    obtain ⟨hg0, hg1, hg2⟩ := hg
    have hdet := g.2
    rw [Matrix.det_fin_three, hg0, hg1, hg2] at hdet
    refine ⟨?_, ?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1, hg2]
    · simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three, hg0, hg1, hg2]
    · simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
      simp [hg0, hg1, hg2]
      linear_combination hdet

end CFSG.Quasithin.RonanH44
