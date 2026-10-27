module

public import Certificates.Data.Holder255.E64Data
public import Certificates.Data.CFSGNative.CosetTable.Enum
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.ClassicalInvolution.Q3.E64Data

open CFSG.CosetTable

@[expose] def q8Rels (j : Nat) : List (List Nat) :=
  [[4 * j, 4 * j, 4 * j, 4 * j], [4 * j, 4 * j, 4 * j + 3, 4 * j + 3],
    [4 * j + 2, 4 * j, 4 * j + 3, 4 * j]]

@[expose] def conjRel (d : Nat × Nat × Nat × Nat × List Nat) : List Nat :=
  [2 * d.1, 2 * (2 * d.2.1 + d.2.2.1), 2 * d.1 + 1] ++
    (d.2.2.2.2.reverse.map fun l => 2 * (2 * d.2.2.2.1 + l) + 1)

@[expose] def e64Rels (_ : Unit := ()) : List (List Nat) :=
  (List.range 14).flatMap q8Rels ++ e64ConjData.map conjRel

end CFSG.ClassicalInvolution.Q3.E64Data
