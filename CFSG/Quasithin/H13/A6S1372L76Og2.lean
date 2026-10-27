module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3F2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.SmithB45Alt7IndData

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Matrix

namespace A6L76Og

variable {F : Type} [Field F] [CharP F 2]

theorem sq_eq_trace (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    M * M = M.trace • M + 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_two] at hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  · linear_combination (-1 : F) * hM + (-1 : F) * h2
  · ring
  · ring
  · linear_combination (-1 : F) * hM + (-1 : F) * h2

theorem trace_pow_three (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    (M ^ 3).trace = M.trace ^ 3 + M.trace := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq := sq_eq_trace M hM
  have h3 : M ^ 3 = (M.trace ^ 2 + 1) • M + M.trace • 1 := by
    rw [pow_three, hsq, Matrix.mul_add, Matrix.mul_smul, hsq, Matrix.mul_one, smul_add,
      smul_smul, add_smul, one_smul, pow_two]
    abel
  rw [h3, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul, smul_eq_mul]
  push_cast
  linear_combination M.trace * h2

theorem trace_of_pow_eq_one (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) {m : ℕ}
    (h : M ^ (3 * 2 ^ m) = 1) : M.trace = 0 ∨ M.trace = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hD : (M ^ 3) ^ (2 ^ m) = 1 := by rw [← pow_mul, h]
  have hnil : IsNilpotent (M ^ 3 - 1) := by
    refine ⟨2 ^ m, ?_⟩
    rw [sub_pow_char_pow_of_commute 2 m (Commute.one_right _), hD, one_pow, sub_self]
  have htr := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, trace_pow_three M hM] at htr
  push_cast at htr
  have h3 : M.trace * ((M.trace + 1) * (M.trace + 1)) = 0 := by
    linear_combination htr + (M.trace ^ 2 + 1) * h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact Or.inl h4
  · right
    have h5 := mul_self_eq_zero.1 h4
    linear_combination h5 - h2

@[expose] def sl2A : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 1]

@[expose] def sl2B (c : F) : Matrix (Fin 2) (Fin 2) F := !![c, 1; c ^ 2 + c + 1, c + 1]

omit [CharP F 2] in
theorem trace_sl2A : (sl2A : Matrix (Fin 2) (Fin 2) F).trace = 1 := by
  rw [sl2A, Matrix.trace_fin_two_of, zero_add]

theorem det_sl2A : (sl2A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sl2A, Matrix.det_fin_two_of]
  linear_combination (-1 : F) * h2

theorem trace_sl2B (c : F) : (sl2B c).trace = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sl2B, Matrix.trace_fin_two_of]
  linear_combination c * h2

theorem det_sl2B (c : F) : (sl2B c).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sl2B, Matrix.det_fin_two_of]
  linear_combination (-1 : F) * h2

theorem trace_sl2A_mul_sl2B (c : F) : (sl2A * sl2B c).trace = c ^ 2 + 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [sl2A, sl2B, Matrix.mul_fin_two, Matrix.trace_fin_two_of]
  linear_combination (c + 1) * h2

theorem pow_three_of_trace_one {M : Matrix (Fin 2) (Fin 2) F} (hM : M.det = 1)
    (h1 : M.trace = 1) : M ^ 3 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq := sq_eq_trace M hM
  rw [h1, one_smul] at hsq
  rw [pow_three, hsq, Matrix.mul_add, hsq, Matrix.mul_one]
  have hMM : M + M = 0 := by rw [← two_smul F M, h2, zero_smul]
  calc M + 1 + M = (M + M) + 1 := by abel
    _ = 1 := by rw [hMM, zero_add]

theorem trace_sl2A_mul_sl2B_ne {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (sl2A * sl2B c).trace ≠ 0 ∧ (sl2A * sl2B c).trace ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [trace_sl2A_mul_sl2B]
  refine ⟨fun h => hc1 ?_, fun h => hc0 ?_⟩
  · have h3 : (c + 1) * (c + 1) = 0 := by linear_combination h + c * h2
    linear_combination mul_self_eq_zero.1 h3 - h2
  · have h3 : c * c = 0 := by linear_combination h
    exact mul_self_eq_zero.1 h3

theorem isSimpleGroup_sl2 [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hs4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr hs4)
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
    obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [Fintype.card_fin] at hr
    have hr1 : r = 1 := by
      have h3 : (r + 1) * (r + 1) = 0 := by linear_combination hr + (r + 1) * h2
      linear_combination mul_self_eq_zero.1 h3 - h2
    rw [hr1] at hrA
    ext i j
    rw [← hrA]
    simp [Matrix.one_apply]
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

end A6L76Og

end CFSG.Quasithin.H13.A6
