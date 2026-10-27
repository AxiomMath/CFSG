module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2That

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 L0S image_lineSet lineSet_eq_of_sameSet repL_x)

@[expose] def invIdx : List ℕ :=
  [3, 4, 5, 6, 9, 14, 17, 18, 19, 20, 21, 24, 25, 26, 28, 29, 33, 34, 36, 40, 50, 53, 54, 56, 57,
    58, 61, 64, 67, 70, 84, 88, 91, 92, 93, 98, 99, 100, 105, 109, 114, 122, 125]

@[expose] def invTgt : List ℕ :=
  [0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 2, 3, 3, 2, 3,
    3, 3, 2, 3, 3, 2, 3, 3, 3, 3, 3]

@[expose] def invW : List (List ℕ) :=
  [[1, 3, 2, 3, 2, 2], [2, 3, 2, 3, 0, 1, 1], [2, 3, 2, 3, 2, 2, 0, 1], [],
    [2, 0, 1, 1, 0, 2, 0, 2], [2, 3, 2, 3, 2, 0, 2], [2, 3, 0, 1, 1, 0, 1], [2, 0, 1, 1, 0, 1, 1],
    [2, 0, 2, 0, 1, 1, 3, 2], [], [1, 3, 1, 0, 2, 0, 2], [1, 3, 2, 2], [2, 0, 1, 1, 3, 1, 3, 1],
    [2, 0, 2, 2, 3, 0, 1], [2, 3, 1, 0, 2, 3, 1], [1, 3, 1, 3, 1, 3, 1], [2, 0, 1, 0, 2],
    [2, 0, 2, 0, 1, 0, 1], [2, 3, 2, 3, 2, 3, 2], [1, 3, 0, 2], [1, 3, 0, 1, 0, 2, 3, 1],
    [1, 3, 2, 0, 1], [2, 2, 3, 1, 1], [1, 3, 2, 2], [1, 1, 3, 2], [1, 3, 0, 1, 1, 3, 1, 1],
    [1, 0, 1, 1, 0, 2, 0, 1], [], [1, 0, 2, 3, 1, 0, 2], [], [1, 3, 2, 3, 2, 2],
    [2, 0, 2, 3, 2, 2, 3, 1], [2, 3, 1, 0, 1, 1, 0, 1, 0, 2], [2, 0, 2, 0, 1, 0, 1],
    [2, 3, 1, 0, 2, 3, 1], [2, 3, 1, 0, 2, 3, 1], [1, 0, 2, 2, 0, 2, 3, 0, 1],
    [2, 0, 2, 0, 1, 0, 1], [2, 3, 1, 0, 2, 3, 0, 2, 3], [2, 3, 1, 0, 2, 3, 0, 2],
    [1, 3, 2, 3, 2, 2], [1, 0, 1, 0, 2, 0, 2], [2, 2, 0, 2, 0, 1, 0, 1, 0, 1]]

@[expose] def invL (k : ℕ) : PL := Thl.getD (invIdx.getD k 0) []

@[expose] def invRep : List PL := [Tl.getD 6 [], Tl.getD 20 [], fhatL, comp fhatL xL]

theorem invRep_x : invRep.getD 0 [] = xL := by decide +kernel

theorem t0L_mem : Tl.getD 20 [] ∈ Thl := by decide +kernel

theorem inv_check :
    (∀ k < 43, comp (invL k) (invL k) = idL ∧ invL k ≠ idL ∧
      comp (comp (evalAL (invW.getD k [])) (invL k)) (evalAL (invAL (invW.getD k []))) =
        invRep.getD (invTgt.getD k 0) [] ∧
      ((evalAL (invW.getD k [])).getD 0 0 = 0 ∨
        sameSet (imgSet (evalAL (invW.getD k [])) L0) L0 = true)) ∧
    (∀ l ∈ Thl, comp l l = idL → l ≠ idL → ∃ k < 43, l = invL k) ∧
    (∀ k < 43, invTgt.getD k 0 < 4) := by
  decide +kernel

end CFSG.Quasithin.H13.F431.U42Aut
