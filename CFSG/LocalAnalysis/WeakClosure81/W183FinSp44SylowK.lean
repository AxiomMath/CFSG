module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44Refine
public import CFSG.LocalAnalysis.WeakClosure81.W183FinSp44PackK

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Sp44

theorem scal_lt_K (a b : Nat) (ha : a < 4) (hb : b < 2 ^ 8) : scal a b < 2 ^ 8 := by
  have h : ∀ a' : Fin 4, ∀ b' : Fin 256, scal a'.val b'.val < 2 ^ 8 := by decide +kernel
  exact h ⟨a, ha⟩ ⟨b, hb⟩

theorem mulRow_lt_K (r B : Nat) : mulRow r B < 2 ^ 8 := by
  have hs : ∀ k, scal (ent r k) (row B k) < 2 ^ 8 := fun k =>
    scal_lt_K _ _ (ent_lt r k) (by unfold row; exact Nat.and_lt_two_pow _ (by norm_num))
  unfold mulRow
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hs 0) (hs 1)) (hs 2)) (hs 3)

theorem mmul_lt_K (A B : Nat) : mmul A B < 4294967296 := by
  have hs : ∀ x k, x < 2 ^ 8 → k ≤ 24 → x <<< k < 2 ^ 32 := fun x k hx hk => by
    rw [Nat.shiftLeft_eq]
    calc x * 2 ^ k < 2 ^ 8 * 2 ^ k := by gcongr
      _ = 2 ^ (8 + k) := (Nat.pow_add 2 8 k).symm
      _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h0 : mulRow (row A 0) B < 2 ^ 32 := lt_of_lt_of_le (mulRow_lt_K _ _) (by norm_num)
  have h : mmul A B < 2 ^ 32 := by
    unfold mmul
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h0
      (hs _ 8 (mulRow_lt_K _ _) (by norm_num))) (hs _ 16 (mulRow_lt_K _ _) (by norm_num)))
      (hs _ 24 (mulRow_lt_K _ _) (by norm_num))
  simpa using h

theorem mmul_assoc_K (A B C : Nat) : mmul (mmul A B) C = mmul A (mmul B C) :=
  decodeM_inj (mmul_lt_K _ _) (mmul_lt_K _ _) (by
    rw [decodeM_mmul, decodeM_mmul, decodeM_mmul, decodeM_mmul, Matrix.mul_assoc])

end CFSG.LocalAnalysis.WeakClosure81.Sp44

end
