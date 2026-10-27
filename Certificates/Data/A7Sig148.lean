module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Perm

public section

open Equiv

namespace A7Sig148

@[expose] def c1 : Perm (Fin 7) := swap 0 2 * swap 0 1

@[expose] def c2 : Perm (Fin 7) := swap 3 5 * swap 3 4

@[expose] def E0l : List (Perm (Fin 7)) :=
  [1, c2, c2 ^ 2, c1, c1 * c2, c1 * c2 ^ 2, c1 ^ 2, c1 ^ 2 * c2, c1 ^ 2 * c2 ^ 2]

@[expose] def V1l : List (Perm (Fin 7)) :=
  [1, swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5]

@[expose] def V2l : List (Perm (Fin 7)) :=
  [1, swap 0 1 * swap 2 6, swap 0 2 * swap 1 6, swap 0 6 * swap 1 2]

@[expose] def gens : List (Perm (Fin 7)) := V1l.tail ++ V2l.tail

@[expose] def wordProd (w : List ℕ) : Perm (Fin 7) := (w.map fun i => gens.getD i 1).prod

@[expose] def words : List (List ℕ) :=
  [[3, 0, 3, 2, 3, 1, 3], [3, 1, 3, 2, 3, 0, 3], [0, 3, 1, 3, 2, 3, 0, 3], [3, 1, 3, 0, 3, 2, 3],
    [0, 3, 2, 3, 1, 3, 0, 3], [3, 0, 3, 1, 3, 2, 3], [3, 2, 3, 0, 3, 1, 3],
    [3, 2, 3, 1, 3, 0, 3], [1, 3, 0, 3, 2], [0, 3, 1, 3, 2], [3, 2, 3, 2], [2, 3, 0, 3, 1],
    [0, 3, 2, 3, 1], [3, 1, 3, 1], [2, 3, 1, 3, 0], [1, 3, 2, 3, 0], [3, 0, 3, 0], [2, 3, 2, 3],
    [1, 3, 1, 3], [0, 3, 0, 3], [3, 2, 5, 2, 4], [3, 1, 5, 1, 4], [3, 0, 5, 0, 4],
    [0, 3, 0, 5, 0, 4, 0], [4, 2, 5, 2, 3], [1, 4, 0, 4, 2], [0, 4, 1, 4, 2], [4, 2, 4, 2],
    [4, 1, 5, 1, 3], [2, 4, 0, 4, 1], [0, 4, 2, 4, 1], [4, 1, 4, 1], [4, 0, 5, 0, 3],
    [2, 4, 1, 4, 0], [1, 4, 2, 4, 0], [4, 0, 4, 0], [0, 4, 0, 5, 0, 3, 0], [2, 4, 2, 4],
    [1, 4, 1, 4], [0, 4, 0, 4], [0, 3, 0, 4, 0, 5, 0, 3], [4, 2, 3, 2, 5], [4, 1, 3, 1, 5],
    [4, 0, 3, 0, 5], [0, 4, 0, 3, 0, 5, 0], [0, 3, 0, 5, 0, 4, 0, 3], [3, 2, 4, 2, 5],
    [3, 1, 4, 1, 5], [3, 0, 4, 0, 5], [0, 3, 0, 4, 0, 5, 0], [5, 2, 3, 2, 4], [5, 2, 4, 2, 3],
    [1, 5, 0, 5, 2], [0, 5, 1, 5, 2], [5, 2, 5, 2], [5, 1, 3, 1, 4], [5, 1, 4, 1, 3],
    [2, 5, 0, 5, 1], [0, 5, 2, 5, 1], [5, 1, 5, 1], [5, 0, 3, 0, 4], [5, 0, 4, 0, 3],
    [2, 5, 1, 5, 0], [1, 5, 2, 5, 0], [5, 0, 5, 0], [0, 5, 0, 3, 0, 4, 0], [0, 5, 0, 4, 0, 3, 0],
    [2, 5, 2, 5], [1, 5, 1, 5], [0, 5, 0, 5]]

@[expose] def MulClosed (l : List (Perm (Fin 7))) : Prop := ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l

instance (l : List (Perm (Fin 7))) : Decidable (MulClosed l) := by
  unfold MulClosed; infer_instance

@[expose] def InvClosed (l : List (Perm (Fin 7))) : Prop := ∀ a ∈ l, a⁻¹ ∈ l

instance (l : List (Perm (Fin 7))) : Decidable (InvClosed l) := by
  unfold InvClosed; infer_instance

@[expose] def Even (l : List (Perm (Fin 7))) : Prop := ∀ a ∈ l, Perm.sign a = 1

instance (l : List (Perm (Fin 7))) : Decidable (Even l) := by unfold Even; infer_instance

@[expose] def Comm (l : List (Perm (Fin 7))) : Prop := ∀ a ∈ l, ∀ b ∈ l, a * b = b * a

instance (l : List (Perm (Fin 7))) : Decidable (Comm l) := by unfold Comm; infer_instance

@[expose] def expE0 : Prop := ∀ a ∈ E0l, a ^ 3 = 1

instance : Decidable expE0 := by unfold expE0; infer_instance

@[expose] def centCheck : Prop :=
  ∀ x ∈ E0l, x ≠ 1 → ∀ g : Perm (Fin 7), Perm.sign g = 1 → g * x = x * g →
    g ^ 6 = 1 ∧ (g ^ 2 = 1 → g ∈ V1l ∨ g ∈ V2l)

instance : Decidable centCheck := by unfold centCheck; infer_instance

@[expose] def Orb (l : List (Perm (Fin 7))) : Prop :=
  ∀ t ∈ l, t ≠ 1 → ∀ u ∈ l, u = 1 ∨ ∃ y ∈ E0l, u = y * t * y⁻¹

instance (l : List (Perm (Fin 7))) : Decidable (Orb l) := by unfold Orb; infer_instance

@[expose] def wordsOK : Prop :=
  ∀ σ : Perm (Fin 7), σ.cycleType = {3} → ∃ w ∈ words, wordProd w = σ

instance : Decidable wordsOK := by unfold wordsOK; infer_instance

@[expose] def stmt : Prop :=
  MulClosed E0l ∧ InvClosed E0l ∧ E0l.Nodup ∧ Even E0l ∧ expE0 ∧
    MulClosed V1l ∧ InvClosed V1l ∧ Even V1l ∧ Comm V1l ∧
    MulClosed V2l ∧ InvClosed V2l ∧ Even V2l ∧ Comm V2l ∧
    centCheck ∧ Orb V1l ∧ Orb V2l ∧ wordsOK

instance : Decidable stmt := by unfold stmt; infer_instance

@[expose] def check : Bool := decide stmt

end A7Sig148
