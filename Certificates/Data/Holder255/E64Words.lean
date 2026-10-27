module

public import Certificates.Data.Holder255.E64Data

public section

namespace CFSG.ClassicalInvolution.Q3.E64Data

@[expose] def e64Letter (c : Nat) : Fin 28 × Bool := (Fin.ofNat 28 (c / 2), c % 2 == 0)

@[expose] def e64Q8Codes (j : Nat) : List (List Nat) :=
  [[4 * j, 4 * j, 4 * j, 4 * j], [4 * j, 4 * j, 4 * j + 3, 4 * j + 3],
    [4 * j + 2, 4 * j, 4 * j + 3, 4 * j]]

@[expose] def e64ConjCodes (d : Nat × Nat × Nat × Nat × List Nat) : List Nat :=
  [2 * d.1, 2 * (2 * d.2.1 + d.2.2.1), 2 * d.1 + 1] ++
    (d.2.2.2.2.reverse.map fun l => 2 * (2 * d.2.2.2.1 + l) + 1)

@[expose] def e64Words : List (List (Fin 28 × Bool)) :=
  ((List.range 14).flatMap e64Q8Codes ++ e64ConjData.map e64ConjCodes ++ [e64Partner]).map
    fun w : List Nat => w.map e64Letter

end CFSG.ClassicalInvolution.Q3.E64Data
