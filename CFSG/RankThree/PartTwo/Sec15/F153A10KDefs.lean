module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv

@[expose] def tZero : Perm (Fin 10) := swap 0 1 * swap 2 3

@[expose] def tOne : Perm (Fin 10) := swap 0 1 * swap 2 3 * swap 5 6 * swap 7 8

@[expose] def taA : Perm (Fin 10) := swap 0 2 * swap 1 3

@[expose] def tbB : Perm (Fin 10) := swap 0 1 * swap 4 5

@[expose] def gZero : Perm (Fin 10) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def gOne : Perm (Fin 10) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * (swap 5 6 * swap 6 7 * swap 7 8 * swap 8 9)

@[expose] def hOne : Perm (Fin 10) := swap 5 6 * swap 6 7 * swap 7 8 * swap 8 9

@[expose] def gA : Perm (Fin 10) := swap 0 4 * swap 1 5 * swap 2 6 * swap 7 8

@[expose] def hA : Perm (Fin 10) := swap 0 6 * swap 1 7 * swap 2 8 * swap 3 9

@[expose] def gB : Perm (Fin 10) :=
  swap 1 9 * swap 9 4 * swap 4 7 * swap 7 5 * swap 5 3 * swap 3 8

@[expose] def hB : Perm (Fin 10) := swap 2 6 * swap 6 8 * swap 8 4 * swap 4 9

@[expose] def P2Stmt : Prop :=
  ∀ E : Subgroup (Perm (Fin 10)), E ≤ alternatingGroup (Fin 10) → Nat.card E = 2 →
    ∃ g ∈ alternatingGroup (Fin 10), 5 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj g).toMonoidHom)

@[expose] def P4Stmt : Prop :=
  ∀ E : Subgroup (Perm (Fin 10)), E ≤ alternatingGroup (Fin 10) → (∀ a ∈ E, a ^ 2 = 1) →
    Nat.card E = 4 →
    ∃ g ∈ alternatingGroup (Fin 10), ∃ h ∈ alternatingGroup (Fin 10),
      25 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj g).toMonoidHom ⊔ E.map (MulAut.conj h).toMonoidHom)

end CFSG.RankThree.PartTwo.Sec15.F153A10K
