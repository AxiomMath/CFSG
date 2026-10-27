module

public import Certificates.Data.Holder272.E29Data

public section

namespace CFSG.ClassicalInvolution.Q3.E29Data

@[expose] def e29Letter (c : Nat) : Fin 56 × Bool := (Fin.ofNat 56 (c / 2), c % 2 == 0)

@[expose] def e29Q8Codes (j : Nat) : List (List Nat) :=
  [[4 * j, 4 * j, 4 * j, 4 * j], [4 * j, 4 * j, 4 * j + 3, 4 * j + 3],
    [4 * j + 2, 4 * j, 4 * j + 3, 4 * j]]

@[expose] def e29ConjCodes (d : Nat × Nat × Nat × Nat × List Nat) : List Nat :=
  [2 * d.1, 2 * (2 * d.2.1 + d.2.2.1), 2 * d.1 + 1] ++
    (d.2.2.2.2.reverse.map fun l => 2 * (2 * d.2.2.2.1 + l) + 1)

@[expose] def e29Words : List (List (Fin 56 × Bool)) :=
  ((List.range 28).flatMap e29Q8Codes ++ e29ConjData.map e29ConjCodes ++
      e29Partners.map fun p => [0, 0, 4 * p + 1, 4 * p + 1]).map
    fun w : List Nat => w.map e29Letter

end CFSG.ClassicalInvolution.Q3.E29Data
