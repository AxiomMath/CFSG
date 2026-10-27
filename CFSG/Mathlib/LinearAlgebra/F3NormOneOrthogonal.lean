module
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring.RingNF

public section
namespace Matrix
variable {ι : Type*} [Fintype ι]
private theorem dot_add_self (x y : ι → ZMod 3) :
    (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + y ⬝ᵥ y + 2 * (x ⬝ᵥ y) := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]
  ring
private theorem dot_sub_self (x y : ι → ZMod 3) :
    (x - y) ⬝ᵥ (x - y) = x ⬝ᵥ x + y ⬝ᵥ y - 2 * (x ⬝ᵥ y) := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm y x]
  ring
private theorem scalar_zero : ∀ d : ZMod 3,
    2 + 2 * d ≠ 1 → 2 - 2 * d ≠ 1 → d = 0 := by
  decide +kernel
theorem transpose_mul_self_of_dot_self_one_iff (M : Matrix ι ι (ZMod 3))
    [DecidableEq ι]
    (h : ∀ v : ι → ZMod 3, (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = 1 ↔ v ⬝ᵥ v = 1) :
    Mᵀ * M = 1 := by
  have hcol : ∀ i, M.col i ⬝ᵥ M.col i = 1 := by
    intro i
    have hi := (h (Pi.single i 1)).2 (by simp)
    simpa only [Matrix.mulVec_single_one] using hi
  have horth : ∀ i j, i ≠ j → M.col i ⬝ᵥ M.col j = 0 := by
    intro i j hij
    have hplus : (Pi.single i 1 + Pi.single j 1 : ι → ZMod 3) ⬝ᵥ
        (Pi.single i 1 + Pi.single j 1 : ι → ZMod 3) = 2 := by
      rw [dot_add_self]
      simp [hij.symm]
      ring
    have hminus : (Pi.single i 1 - Pi.single j 1 : ι → ZMod 3) ⬝ᵥ
        (Pi.single i 1 - Pi.single j 1 : ι → ZMod 3) = 2 := by
      rw [dot_sub_self]
      simp [hij.symm]
      ring
    apply scalar_zero
    · intro heq
      have hi : (M *ᵥ (Pi.single i 1 + Pi.single j 1)) ⬝ᵥ
          (M *ᵥ (Pi.single i 1 + Pi.single j 1)) = 1 := by
        rw [Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
          dot_add_self, hcol i, hcol j]
        convert heq using 1; ring
      have hb := (h _).1 hi
      rw [hplus] at hb
      exact (by decide : (2 : ZMod 3) ≠ 1) hb
    · intro heq
      have hi : (M *ᵥ (Pi.single i 1 - Pi.single j 1)) ⬝ᵥ
          (M *ᵥ (Pi.single i 1 - Pi.single j 1)) = 1 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
          dot_sub_self, hcol i, hcol j]
        convert heq using 1; ring
      have hb := (h _).1 hi
      rw [hminus] at hb
      exact (by decide : (2 : ZMod 3) ≠ 1) hb
  ext i j
  rw [Matrix.one_apply]
  change M.col i ⬝ᵥ M.col j = if i = j then 1 else 0
  by_cases hij : i = j
  · subst j
    simpa using hcol i
  · simpa only [if_neg hij] using horth i j hij
end Matrix
