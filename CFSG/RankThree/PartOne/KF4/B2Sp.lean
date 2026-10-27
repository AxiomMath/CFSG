module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor

public section

namespace CFSG.RankThree.PartOne.KF4

open Matrix

variable (K : Type) [Field K]

@[expose] def f4B2J0 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, -1, 0; 0, 1, 0, 0; -1, 0, 0, 0]

@[expose] def f4SpGroup : Subgroup (GL (Fin 4) K) where
  carrier := {A | (A : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * (A : Matrix (Fin 4) (Fin 4) K) =
    f4B2J0 K}
  one_mem' := by
    change (1 : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * 1 = f4B2J0 K
    rw [transpose_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' := by
    intro g h hg hh
    change ((g : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K))ᵀ * f4B2J0 K *
      ((g : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K)) = f4B2J0 K
    calc ((g : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K))ᵀ * f4B2J0 K *
          ((g : Matrix (Fin 4) (Fin 4) K) * (h : Matrix (Fin 4) (Fin 4) K))
        = (h : Matrix (Fin 4) (Fin 4) K)ᵀ * ((g : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K *
            (g : Matrix (Fin 4) (Fin 4) K)) * (h : Matrix (Fin 4) (Fin 4) K) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by
          rw [show (g : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * (g : Matrix (Fin 4) (Fin 4) K) =
            f4B2J0 K from hg]
          exact hh
  inv_mem' := by
    intro g hg
    change ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K *
      ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = f4B2J0 K
    have hg' : (g : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * (g : Matrix (Fin 4) (Fin 4) K) =
      f4B2J0 K := hg
    have hAB : (g : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = 1 := g.mul_inv
    calc ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
            ((g : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * (g : Matrix (Fin 4) (Fin 4) K)) *
            ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [hg']
      _ = ((g : Matrix (Fin 4) (Fin 4) K) *
            ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ * f4B2J0 K *
          ((g : Matrix (Fin 4) (Fin 4) K) *
            ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = f4B2J0 K := by rw [hAB, transpose_one, Matrix.one_mul, Matrix.mul_one]

variable {K}

theorem mem_f4SpGroup {A : GL (Fin 4) K} :
    A ∈ f4SpGroup K ↔
      (A : Matrix (Fin 4) (Fin 4) K)ᵀ * f4B2J0 K * (A : Matrix (Fin 4) (Fin 4) K) = f4B2J0 K :=
  Iff.rfl

theorem f4B2J0_eq_minorJ [CharP K 2] :
    f4B2J0 K = CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorJ K := by
  have h : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [f4B2J0, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.minorJ_apply, h]

theorem f4SpGroup_eq_antiSp [CharP K 2] :
    f4SpGroup K = CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSp K := by
  ext A
  rw [mem_f4SpGroup, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.mem_antiSp,
    f4B2J0_eq_minorJ]

end CFSG.RankThree.PartOne.KF4
