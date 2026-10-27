module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartTwo.Sec21

private theorem coe_sl2OrderThree_inv {K : Type} [Field K] [CharP K 2] :
    (((sl2OrderThree (F := K))⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 1; 1, 0] := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : sl2OrderThree (F := K) ^ 3 = 1 := by
    rw [← orderOf_sl2OrderThree (F := K)]
    exact pow_orderOf_eq_one _
  have hmul : sl2OrderThree (F := K) * sl2OrderThree ^ 2 = 1 := by
    have h := h3
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ'] at h
    exact h
  rw [inv_eq_of_mul_eq_one_right hmul, pow_two, Matrix.SpecialLinearGroup.coe_mul,
    coe_sl2OrderThree, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2] <;> linear_combination h2

private theorem coe_leviSp_sl2OrderThree {K : Type} [Field K] [CharP K 2] :
    (((leviSp (r := 2) (k := K)
        (Matrix.SpecialLinearGroup.toGL (sl2OrderThree (F := K))) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks !![0, 1; 1, 1] 0 0 !![1, 1; 1, 0] := by
  rw [coe_leviSp, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_sl2OrderThree]
  congr 2
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_sl2OrderThree_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem exists_orderOf_three_fieldAut_fixed (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) :
    ∃ x : StatedProj (StatedSp 2 K), orderOf x = 3 ∧ fieldAut 2 K σ x = x := by
  let g₀ : StatedSp 2 K :=
    leviSp (r := 2) (k := K) (Matrix.SpecialLinearGroup.toGL (sl2OrderThree (F := K)))
  have hg₀ : ((g₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks !![0, 1; 1, 1] 0 0 !![1, 1; 1, 0] :=
    coe_leviSp_sl2OrderThree
  have hg3 : g₀ ^ 3 = 1 := by
    have hM3 : sl2OrderThree (F := K) ^ 3 = 1 := by
      rw [← orderOf_sl2OrderThree (F := K)]
      exact pow_orderOf_eq_one _
    rw [show g₀ = leviSp (r := 2) (k := K)
      (Matrix.SpecialLinearGroup.toGL (sl2OrderThree (F := K))) from rfl]
    rw [← map_pow, ← map_pow (Matrix.SpecialLinearGroup.toGL), hM3, map_one, map_one]
  have hg00 : ((g₀ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inl 0) = 0 := by
    rw [coe_leviSp, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_sl2OrderThree]
    simp
  have hxne : proj 2 K g₀ ≠ 1 := by
    intro h
    have hker : g₀ ∈ (proj 2 K).ker := h
    rw [ker_proj] at hker
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hker
    obtain ⟨c, hc⟩ := hker
    rw [← hc] at hg00
    simp [Matrix.GeneralLinearGroup.coe_scalar] at hg00
  have hfix : fieldSp 2 K σ g₀ = g₀ := by
    apply statedSp_ext
    rw [coe_fieldSp]
    ext x y
    rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hg₀, Matrix.map_apply, CharP.cast_eq_zero K 2]
  refine ⟨proj 2 K g₀, ?_, ?_⟩
  · refine orderOf_eq_prime ?_ hxne
    rw [← map_pow, hg3, map_one]
  · rw [fieldAut_proj, hfix]

end CFSG.RankThree.PartTwo.KFacts

end
