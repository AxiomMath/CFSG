module

public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.AllConj

@[expose] def vS : Fin 5 → ℕ := ![1, 0, 0, 0, 0]

@[expose] def vE : Fin 5 → Fin 8 → ℕ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0, 1, 1, 0], ![0, 1, 0, 0, 1, 1, 0, 0]]

@[expose] def rowsV (j : Fin 5) : Array V4 := rowsNf (vS j) (vE j)

@[expose] def rowsIota (c : Fin 5 → ℕ) : Array V4 :=
  prodRows (List.ofFn fun j => powRows (rowsV j) (c j))

@[expose] def rowsA1 : Array V4 := mulRows (powRows rowsY 5) rowsX

@[expose] def rowsA2 : Array V4 := mulRows (mulRows rowsY rowsX) (powRows rowsY 5)

@[expose] def gWord : List ℕ := [1, 2, 2, 1, 2]

@[expose] def rowsA3 : Array V4 :=
  mulRows (mulRows (abRows gWord)
    (powRows (mulRows rowsA (mulRows (mulRows (abRows (invWord gWord)) (rowsQ 0)) (abRows gWord)))
      9)) (powRows rowsY 4)

@[expose] def colA1 : Fin 5 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 0, 0, 1], ![1, 0, 0, 1, 1]]

@[expose] def colA2 : Fin 5 → Fin 5 → ℕ :=
  ![![1, 0, 0, 0, 0], ![1, 0, 1, 1, 1], ![1, 1, 0, 1, 1], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]

@[expose] def colA3 : Fin 5 → Fin 5 → ℕ :=
  ![![0, 1, 0, 0, 0], ![0, 1, 1, 1, 0], ![1, 1, 0, 1, 1], ![1, 1, 0, 0, 0], ![0, 1, 0, 0, 1]]

@[expose] def thFacts : Prop :=
  (∀ j : Fin 5, eqRows (mulRows (rowsV j) (rowsV j)) idRows = true) ∧
  (∀ i j : Fin 5, eqRows (mulRows (rowsV i) (rowsV j)) (mulRows (rowsV j) (rowsV i)) = true) ∧
  (∀ c : Fin 5 → ZMod 2, c ≠ 0 → eqRows (rowsIota fun j => (c j).val) idRows = false) ∧
  (∀ j : Fin 5, eqRows (mulRows rowsA1 (rowsV j)) (mulRows (rowsIota (colA1 j)) rowsA1) = true) ∧
  (∀ j : Fin 5, eqRows (mulRows rowsA2 (rowsV j)) (mulRows (rowsIota (colA2 j)) rowsA2) = true) ∧
  (∀ j : Fin 5, eqRows (mulRows rowsA3 (rowsV j)) (mulRows (rowsIota (colA3 j)) rowsA3) = true)

instance : Decidable thFacts := by
  unfold thFacts
  infer_instance

end CFSG.Sporadic.Recognition.ThMultiplier
