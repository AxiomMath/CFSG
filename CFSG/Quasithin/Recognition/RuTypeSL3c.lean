module

public import CFSG.Quasithin.Recognition.RuTypeSL3

public section

namespace CFSG.Quasithin.RuType.SL3

open scoped MatrixGroups

@[expose] def b0 : SL(3, ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩

@[expose] def c0 : SL(3, ZMod 2) := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩

@[expose] def n0 : SL(3, ZMod 2) := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def g1 : SL(3, ZMod 2) := ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by decide⟩

theorem b0_mem_Stab0 : b0 ∈ Stab0 := by decide +kernel

theorem n0_mem_Stab0 : n0 ∈ Stab0 := by decide +kernel

theorem b0_pow_three : b0 ^ 3 = 1 := by decide +kernel

theorem b0_ne_one : b0 ≠ 1 := by decide +kernel

theorem c0_pow_seven : c0 ^ 7 = 1 := by decide +kernel

theorem c0_ne_one : c0 ≠ 1 := by decide +kernel

theorem b0_c0 : b0 * c0 * b0⁻¹ = c0 ^ 2 := by decide +kernel

theorem stAct_pow (g : SL(3, ZMod 2)) (k : ℕ) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    stAct (g ^ k) A = (stAct g)^[k] A := by
  induction k with
  | zero => rw [pow_zero, stAct_one, Function.iterate_zero, id]
  | succ k ih => rw [pow_succ', stAct_mul, ih, Function.iterate_succ_apply']

theorem natAct3_pow (g : SL(3, ZMod 2)) (k : ℕ) (v : Fin 3 → ZMod 2) :
    natAct3 (g ^ k) v = (natAct3 g)^[k] v := by
  induction k with
  | zero => rw [pow_zero, natAct3_one, Function.iterate_zero, id]
  | succ k ih => rw [pow_succ', natAct3_mul, ih, Function.iterate_succ_apply']

theorem c0_fix_vec : ∀ v : Fin 3 → ZMod 2, natAct3 c0 v = v → v = 0 := by decide +kernel

theorem b0_fix_vec : ∀ v : Fin 3 → ZMod 2, natAct3 b0 v = v → v = 0 ∨ v = e0 := by
  decide +kernel

theorem c0_cubic'_vec : ∀ v : Fin 3 → ZMod 2,
    natAct3 c0 (natAct3 c0 (natAct3 c0 v)) + natAct3 c0 (natAct3 c0 v) + v = 0 → v = 0 := by
  decide +kernel

theorem c0_trans_vec : ∀ v w : Fin 3 → ZMod 2, (v ≠ 0 ∧ w ≠ 0) →
    ∃ k : Fin 7, w = (natAct3 c0)^[k.val] v := by
  decide +kernel

@[expose] def fixC0List : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [0, !![0, 0, 1; 1, 0, 1; 0, 1, 0], !![0, 1, 0; 0, 1, 1; 1, 0, 1], !![0, 1, 1; 1, 1, 0; 1, 1, 1]]

@[expose] def st1List : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [0, !![0, 0, 1; 0, 1, 0; 1, 1, 1], !![0, 1, 0; 1, 0, 1; 1, 1, 0], !![0, 1, 1; 1, 1, 1; 0, 0, 1],
    !![1, 0, 0; 0, 0, 1; 0, 1, 1], !![1, 0, 1; 0, 1, 1; 1, 0, 0], !![1, 1, 0; 1, 0, 0; 1, 0, 1],
    !![1, 1, 1; 1, 1, 0; 0, 1, 0]]

theorem fix_c0_iff : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (stAct c0 A = A ↔ A ∈ fixC0List) := by
  decide +kernel

theorem fixC0_props : ∀ A ∈ fixC0List, A.trace = 0 ∧ stAct c0 A = A ∧ stAct b0 A ∈ fixC0List ∧
    (stAct b0 A = A → A = 0) := by
  decide +kernel

theorem fixC0_add : ∀ A ∈ fixC0List, ∀ B ∈ fixC0List, A + B ∈ fixC0List := by decide +kernel

theorem stab_fixC0 : ∀ A ∈ fixC0List, A ≠ 0 → ∀ g : SL(3, ZMod 2), stAct g A = A →
    ∃ k : Fin 7, g = c0 ^ k.val := by
  decide +kernel

theorem st1_props : ∀ A ∈ st1List, A.trace = 0 ∧ stAct c0 A ∈ st1List ∧ stAct b0 A ∈ st1List ∧
    stAct c0 (stAct c0 (stAct c0 A)) + stAct c0 (stAct c0 A) + A = 0 ∧
    ∃ B ∈ st1List, A = B + stAct c0 B := by
  decide +kernel

theorem st1_add : ∀ A ∈ st1List, ∀ B ∈ st1List, A + B ∈ st1List := by decide +kernel

theorem fixC0_st1 : ∀ A ∈ fixC0List, A ∈ st1List → A = 0 := by decide +kernel

theorem c0_trans_st1 : ∀ A ∈ st1List, ∀ B ∈ st1List, (A ≠ 0 ∧ B ≠ 0) →
    ∃ k : Fin 7, B = (stAct c0)^[k.val] A := by
  decide +kernel

theorem fix_b0_iff : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.trace = 0 →
    (stAct b0 A = A ↔ (A = 0 ∨ A = !![0, 0, 0; 0, 1, 0; 0, 0, 1] ∨
      A = !![1, 0, 0; 0, 0, 1; 0, 1, 1] ∨ A = !![1, 0, 0; 0, 1, 1; 0, 1, 0])) := by
  decide +kernel

theorem b0mat_mem_st1 : (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈
    st1List := by
  decide +kernel

theorem n0_swap : stAct n0 !![1, 0, 0; 0, 1, 1; 0, 1, 0] = !![1, 0, 0; 0, 0, 1; 0, 1, 1] := by
  decide +kernel

theorem g1_A1' : stAct g1 !![1, 1, 0; 0, 1, 1; 0, 0, 0] = !![0, 0, 0; 1, 1, 0; 0, 1, 1] := by
  decide +kernel

theorem decomp_A1 : (!![1, 1, 0; 0, 1, 1; 0, 0, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![0, 0, 1; 1, 0, 1; 0, 1, 0] + !![1, 1, 1; 1, 1, 0; 0, 1, 0] := by
  decide +kernel

theorem decomp_B1 : (!![0, 0, 0; 1, 1, 0; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![0, 1, 0; 0, 1, 1; 1, 0, 1] + !![0, 1, 0; 1, 0, 1; 1, 1, 0] := by
  decide +kernel

theorem decomp_B2 : (!![0, 0, 0; 0, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
    !![0, 1, 1; 1, 1, 0; 1, 1, 1] + !![0, 1, 1; 1, 1, 1; 0, 0, 1] := by
  decide +kernel

theorem g1_B2 : ∀ F ∈ fixC0List, ∀ Y ∈ st1List,
    stAct g1 !![0, 0, 0; 0, 0, 1; 1, 1, 0] ≠ F + Y := by
  decide +kernel

end CFSG.Quasithin.RuType.SL3
