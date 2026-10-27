module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import Mathlib.Data.Fintype.Perm
public import CFSG.ClassicalInvolution.Q3.AE.Twins
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open Equiv CFSG.ClassicalInvolution.Q3.AE

@[expose] def InL32 (σ : Perm (Fin 7)) : Prop :=
  ∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧ s.map σ⁻¹.toEmbedding ∈ fanoLines

instance : DecidablePred InL32 := fun σ => by unfold InL32; infer_instance

@[expose] def s7Mu : Perm (Fin 7) :=
  ⟨![0, 6, 5, 3, 4, 2, 1], ![0, 6, 5, 3, 4, 2, 1], by decide, by decide⟩

@[expose] def s7Mu' : Perm (Fin 7) :=
  ⟨![0, 6, 2, 4, 3, 5, 1], ![0, 6, 2, 4, 3, 5, 1], by decide, by decide⟩

@[expose] def s7Tau : Perm (Fin 7) :=
  ⟨![0, 2, 1, 3, 4, 6, 5], ![0, 2, 1, 3, 4, 6, 5], by decide, by decide⟩

@[expose] def s7Xi : Perm (Fin 7) :=
  ⟨![0, 2, 3, 1, 6, 4, 5], ![0, 3, 1, 2, 5, 6, 4], by decide, by decide⟩

@[expose] def s7c1 : Perm (Fin 7) :=
  ⟨![0, 1, 2, 4, 5, 6, 3], ![0, 1, 2, 6, 3, 4, 5], by decide, by decide⟩

@[expose] def s7c2 : Perm (Fin 7) :=
  ⟨![0, 1, 2, 5, 4, 6, 3], ![0, 1, 2, 6, 4, 3, 5], by decide, by decide⟩

@[expose] def s7Letters (g : Perm (Fin 7)) : Fin 5 → Perm (Fin 7) :=
  ![s7Mu, s7Mu', s7Tau, s7Xi, g]

@[expose] def evalWord (gs : Fin 5 → Perm (Fin 7)) : List (Fin 5) → Perm (Fin 7)
  | [] => 1
  | a :: w => gs a * evalWord gs w

@[expose] def wordsOfLength : ℕ → List (List (Fin 5))
  | 0 => [[]]
  | k + 1 => (wordsOfLength k).flatMap fun w => (List.finRange 5).map fun a => w ++ [a]

@[expose] def s7Words (_ : Unit := ()) : List (List (Fin 5)) :=
  (List.range 6).flatMap wordsOfLength

@[expose] def IsOrd5 (σ : Perm (Fin 7)) : Prop := σ ^ 5 = 1 ∧ σ ≠ 1

instance : DecidablePred IsOrd5 := fun σ => by unfold IsOrd5; infer_instance

@[expose] def s7Perms (_ : Unit := ()) : List (Perm (Fin 7)) := permsOfList (List.finRange 7)

@[expose] def s7Ok (W : List (List (Fin 5))) (g : Perm (Fin 7)) : Bool :=
  decide (g 0 = 0) || decide (InL32 (s7c1 * g * s7c1⁻¹)) || decide (InL32 (s7c2 * g * s7c2⁻¹)) ||
    W.any fun w => decide (IsOrd5 (evalWord (s7Letters g) w))

@[expose] def s7CheckW (W : List (List (Fin 5))) (P : List (Perm (Fin 7))) : Bool := P.all (s7Ok W)

@[expose] def s7Check (_ : Unit := ()) : Bool := s7CheckW (s7Words ()) (s7Perms ())

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
