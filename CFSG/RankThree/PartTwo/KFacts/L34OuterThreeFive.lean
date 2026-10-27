module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (coe_diagGL coe_diagGL_inv)
open Matrix

variable {k : Type*} [Field k]

theorem exists_orderOf_five_fixed_xDiag (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) :
    ∃ y : projectiveSL 3 k, orderOf y = 5 ∧ xDiag u y = y := by
  haveI : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hω : (u : k) * u + u + 1 = 0 := val_mul_self_add hk hu
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) k, M = !![1, 0, 0; 0, 0, 1; 0, 1, (u : k)] :=
    ⟨_, rfl⟩
  have hdet : M.det = 1 := by
    rw [hM]
    simp [Matrix.det_fin_three, CharTwo.neg_eq] <;> linear_combination (-1 : k) * h2
  obtain ⟨g, hg⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 3) k,
      (g : Matrix (Fin 3) (Fin 3) k) = M :=
    ⟨⟨M, hdet⟩, rfl⟩
  have hM2 : M * M = !![1, 0, 0; 0, 1, (u : k); 0, (u : k), (u : k)] := by
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination hω - (u : k) * h2
  have hN2 : !![1, 0, 0; 0, 1, (u : k); 0, (u : k), (u : k)] *
      !![1, 0, 0; 0, 1, (u : k); 0, (u : k), (u : k)] =
        !![1, 0, 0; 0, (u : k), 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination hω - (u : k) * h2
        | linear_combination hω - h2
        | linear_combination ((u : k) * u) * h2
  have hP : !![1, 0, 0; 0, (u : k), 1; 0, 1, 0] * M = 1 := by
    rw [hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination (u : k) * h2
  have hM5 : M ^ 5 = 1 := by
    rw [show (5 : ℕ) = 2 + 2 + 1 from rfl, pow_add, pow_add, sq, pow_one, hM2, hN2, hP]
  have hg5 : g ^ 5 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hg, hM5]
  have hns : proj 3 k g ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    have h12 := congrFun (congrFun hc 1) 2
    rw [hg, hM] at h12
    simp [Matrix.scalar_apply] at h12
  refine ⟨proj 3 k g, ?_, ?_⟩
  · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    refine orderOf_eq_prime ?_ hns
    rw [← map_pow, hg5, map_one]
  · rw [xDiag, conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, coe_diagGL, coe_diagGL_inv, hg, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Units.mul_inv]

end CFSG.RankThree.PartTwo.KFacts.L34
