module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.StandardType.ZS

@[expose] def kFiveExp : Fin 5 → Fin 5 → ℕ :=
  ![![1, 3, 2, 2, 2], ![3, 1, 3, 3, 2], ![2, 3, 1, 3, 2], ![2, 3, 3, 1, 3], ![2, 2, 2, 3, 1]]

@[expose] def kSixExp : Fin 6 → Fin 6 → ℕ :=
  ![![1, 3, 2, 2, 2, 2], ![3, 1, 3, 3, 2, 2], ![2, 3, 1, 3, 2, 2], ![2, 3, 3, 1, 3, 2],
    ![2, 2, 2, 3, 1, 3], ![2, 2, 2, 2, 3, 1]]

def HSFiveRel {G : Type*} [Group G] (r : Fin 5 → G) : Prop :=
  (∀ i j, (r i * r j) ^ kFiveExp i j = 1) ∧ (r 2 * r 1 * r 2 * r 3) ^ 3 = 1

def HSSixRel {G : Type*} [Group G] (r : Fin 6 → G) : Prop :=
  (∀ i j, (r i * r j) ^ kSixExp i j = 1) ∧ (r 2 * r 1 * r 2 * r 3) ^ 3 = 1

@[expose] def pairPowWord {m : ℕ} (i j : Fin m) (k : ℕ) : List (Fin m × Bool) :=
  (List.replicate k [(i, true), (j, true)]).flatten

@[expose] def hsFiveRels : List (List (Fin 5 × Bool)) :=
  ((List.finRange 5).flatMap fun i =>
    ((List.finRange 5).filter fun j => decide (i ≤ j)).map fun j =>
      pairPowWord i j (kFiveExp i j)) ++
  [(List.replicate 3 [(2, true), (1, true), (2, true), (3, true)]).flatten]

@[expose] def hsSixRels : List (List (Fin 6 × Bool)) :=
  ((List.finRange 6).flatMap fun i =>
    ((List.finRange 6).filter fun j => decide (i ≤ j)).map fun j =>
      pairPowWord i j (kSixExp i j)) ++
  [(List.replicate 3 [(2, true), (1, true), (2, true), (3, true)]).flatten]

end CFSG.StandardType.ZS

end
