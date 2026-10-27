module

public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs

public section

namespace CFSG.StandardType.ZS

@[expose] def nFourExp : Fin 4 → Fin 4 → ℕ :=
  ![![1, 3, 4, 2], ![3, 1, 3, 2], ![4, 3, 1, 3], ![2, 2, 3, 1]]

@[expose] def enFourExp : Fin 5 → Fin 5 → ℕ :=
  ![![1, 3, 4, 2, 2], ![3, 1, 3, 2, 2], ![4, 3, 1, 3, 2], ![2, 2, 3, 1, 3], ![2, 2, 2, 3, 1]]

@[expose] def posWord {m : ℕ} (l : List (Fin m)) : List (Fin m × Bool) := l.map fun i => (i, true)

@[expose] def n4Extra : List (Fin 4) := [1, 0, 2, 1, 0, 1, 2, 1, 0, 1, 2, 0]

@[expose] def en4Extra : List (Fin 5) :=
  [4, 2, 0, 2, 3, 4, 2, 0, 3, 2, 1, 0, 3, 2, 0, 3, 1, 4, 2, 0, 2, 3, 4, 2, 0, 3, 2, 1]

@[expose] def n4Rels : List (List (Fin 4 × Bool)) :=
  ((List.finRange 4).flatMap fun i =>
    ((List.finRange 4).filter fun j => decide (i ≤ j)).map fun j =>
      pairPowWord i j (nFourExp i j)) ++
  [posWord n4Extra]

@[expose] def en4Rels : List (List (Fin 5 × Bool)) :=
  ((List.finRange 5).flatMap fun i =>
    ((List.finRange 5).filter fun j => decide (i ≤ j)).map fun j =>
      pairPowWord i j (enFourExp i j)) ++
  [posWord (n4Extra.map Fin.castSucc), posWord en4Extra]

@[expose] def N4Rel {M : Type*} [Monoid M] (r : Fin 4 → M) : Prop :=
  (∀ i j, (r i * r j) ^ nFourExp i j = 1) ∧ (n4Extra.map r).prod = 1

@[expose] def EN4Rel {M : Type*} [Monoid M] (r : Fin 5 → M) : Prop :=
  (∀ i j, (r i * r j) ^ enFourExp i j = 1) ∧ ((n4Extra.map Fin.castSucc).map r).prod = 1 ∧
    (en4Extra.map r).prod = 1

@[expose] def n4ZW : List (Fin 4) :=
  [0, 1, 0, 2, 0, 2, 1, 0, 3, 2, 0, 2, 1, 0, 3, 2, 0, 2, 1, 3, 2, 0, 2, 3]

@[expose] def en4ZW : List (Fin 5) := [0, 2, 0, 2, 3, 2, 0, 2, 3, 4, 3, 2, 0, 2, 3, 4]

end CFSG.StandardType.ZS

end
