module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

theorem natCard_submodule_fun_eq_pow_finrank {K : Type*} [Field K] {n : ℕ}
    (S : Submodule K (Fin n → K)) : Nat.card S = Nat.card K ^ Module.finrank K S :=
  Module.natCard_eq_pow_finrank

theorem natCard_submodule_zmod_two {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Nat.card S = 2 ^ Module.finrank (ZMod 2) S := by
  rw [natCard_submodule_fun_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem natCard_submodule_matrix_eq_pow_finrank {K : Type*} [Field K] {n : ℕ}
    (S : Submodule K (Matrix (Fin n) (Fin n) K)) : Nat.card S = Nat.card K ^ Module.finrank K S :=
  Module.natCard_eq_pow_finrank

end CFSG.ASVolI.ChH
