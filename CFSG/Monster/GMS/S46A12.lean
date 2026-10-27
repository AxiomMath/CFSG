module

public import CFSG.Monster.GMS.S36LinesA12

public section

namespace CFSG.Monster.GMS

open Equiv Equiv.Perm S36Lines

namespace S46

private def swapsProd : List (Fin 12 × Fin 12) → Perm (Fin 12)
  | [] => 1
  | (p, q) :: l => swap p q * swapsProd l

private def DisjointSwaps : List (Fin 12 × Fin 12) → Prop
  | [] => True
  | (p, q) :: l => p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l

private instance (l : List (Fin 12 × Fin 12)) : Decidable (DisjointSwaps l) := by
  induction l with
  | nil => exact isTrue trivial
  | cons pq l ih =>
    obtain ⟨p, q⟩ := pq
    exact inferInstanceAs
      (Decidable (p ≠ q ∧ swapsProd l p = p ∧ swapsProd l q = q ∧ DisjointSwaps l))

end S46

end CFSG.Monster.GMS
