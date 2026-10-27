module

public import Certificates.Data.Kernel.SmithD6.StabK
public import Certificates.Data.Kernel.SmithD6.Trees
public import Certificates.Data.SmithD6Model

public section

namespace CFSG.KD.SmithD6Nc

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab

@[expose] def key3 (x y z : Nat) : Nat :=
  let lo := min x (min y z)
  let hi := max x (max y z)
  4096 * lo + (lo ^^^ hi)

@[expose] noncomputable def key3OK (x y z : Nat) : Bool :=
  let lo := min x (min y z)
  let hi := max x (max y z)
  decide (lo < 4096) && decide ((lo ^^^ hi) < 4096) && KT.memB (4096 * lo + (lo ^^^ hi)) lineTree

@[expose] def imgKey (a b : Nat) : Nat :=
  let p := pairK a
  let q := pairK b
  let x1 := sglK p.1 p.2 q.1
  let x2 := sglK p.1 p.2 q.2
  key3 x1 x2 (x1 ^^^ x2)

@[expose] noncomputable def imgOK (a b : Nat) : Bool :=
  let p := pairK a
  let q := pairK b
  let x1 := sglK p.1 p.2 q.1
  let x2 := sglK p.1 p.2 q.2
  key3OK x1 x2 (x1 ^^^ x2)

@[expose] def rootPairs : List (Nat × Nat) :=
  (List.range 6).flatMap fun i => (List.range 6).flatMap fun j =>
    if i < j then [(eV i, eV j), (fV i, fV j), (eV i, fV j), (fV i, eV j)] else []

@[expose] def pairKey (p : Nat × Nat) : Nat := key3 p.1 p.2 (p.1 ^^^ p.2)

@[expose] def stabKeys : List Nat :=
  (rootPairs.map pairKey).filter fun k => k != 4098 && imgKey k 4098 == 4098

@[expose] noncomputable def ncOK : Bool :=
  rootPairs.all (fun p => key3OK p.1 p.2 (p.1 ^^^ p.2) && imgOK (pairKey p) 4098) &&
  stabKeys.length == 42 &&
  imgOK (stabKeys.getD 0 0) (stabKeys.getD 1 0) &&
  imgKey (stabKeys.getD 0 0) (stabKeys.getD 1 0) != stabKeys.getD 1 0

end CFSG.KD.SmithD6Nc

end
