module

public import Certificates.Data.Holder272.E29Data
public import Certificates.Data.CFSGNative.CosetTable.Enum
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.ClassicalInvolution.Q3.E29Data

open CFSG.CosetTable

@[expose] def q8Rels29 (j : Nat) : List (List Nat) :=
  [[4 * j, 4 * j, 4 * j, 4 * j], [4 * j, 4 * j, 4 * j + 3, 4 * j + 3],
    [4 * j + 2, 4 * j, 4 * j + 3, 4 * j]]

@[expose] def conjRel29 (d : Nat × Nat × Nat × Nat × List Nat) : List Nat :=
  [2 * d.1, 2 * (2 * d.2.1 + d.2.2.1), 2 * d.1 + 1] ++
    (d.2.2.2.2.reverse.map fun l => 2 * (2 * d.2.2.2.1 + l) + 1)

@[expose] def partnerRel29 (p : Nat) : List Nat := [0, 0, 4 * p + 1, 4 * p + 1]

@[expose] def e29Rels (_ : Unit := ()) : List (List Nat) :=
  (List.range 28).flatMap q8Rels29 ++ e29ConjData.map conjRel29

@[expose] def e29AllRels (_ : Unit := ()) : List (List Nat) :=
  e29Rels () ++ e29Partners.map partnerRel29

end CFSG.ClassicalInvolution.Q3.E29Data
