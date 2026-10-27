module

public import Certificates.Data.S7TwinCore
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JConditionInputs

public section

namespace Certificates.S7TwinSp6

open CFSG.EvenSmallLie.Sp6 CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native CFSG.ComponentClassification.M12Cover
  Certificates.S7Twin

@[expose] def sylWords : List (List ℤ) :=
  [[-2, -2, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 2, 2], [-2, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2,
    -1, 2, -1, 2, 2, 2], [-2, -2, -1, 2, 2, -1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, -1, 2, -1,
    2, -1, 2, -1, 2, 2, 2], [2, -1, -2, -2, -1, -2, -1, 2, 2, 2, -1, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2,
    2, 1, 2, 1, 2, 1, 2, -1, 2, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1]]

@[expose] def sylGens (_ : Unit := ()) : List (Equiv.Perm (Fin 36)) :=
  sylWords.map fun w => tab (evalCodes sp6Gens w)

@[expose] def sylDerive : List (List ℤ) :=
  [[-3, 2, 3], [-4, 1, 4], [-5, -2, -3, -6, -1, -4, -2, -4, 3, 4, 2, 4]]

@[expose] def sylQ (_ : Unit := ()) : RawSchreierDatum 36 :=
  certificate (by decide) (sylGens ()) sylDerive #v[4, 2, 0, 1] (by decide)

@[expose] def fourWords : List (List ℤ) :=
  [[2, 3, 4, 2, 3, 4], [1, 3, 2, 4, 1, 3, 4, 2], [3, 4, 3, 4, 2], [1, 2, 3, 2, 4, 1, 2, 3, 4], [1,
    2, 3, 4, 2, 3, 4], [1, 3, 4, 3, 4, 2], [2, 4, 2, 3, 4], [1, 4, 1, 3, 2, 4, 2], [2, 4, 3, 4], [1,
    4, 1, 2, 3, 2, 4, 2], [1, 2, 4, 2, 3, 4], [4, 1, 3, 2, 4, 2], [1, 2, 4, 3, 4], [4, 1, 2, 3, 2,
    4, 2], [2, 3, 4, 2, 4, 3, 4], [2, 4], [3, 2, 4, 2, 4, 3, 4, 2], [1, 4], [1, 2, 3, 2, 4, 2, 4, 3,
    4, 2], [1, 2, 3, 4, 2, 4, 3, 4], [1, 2, 4], [1, 3, 2, 4, 2, 4, 3, 4, 2], [1, 3, 4, 2, 4, 3, 4],
    [4, 3], [1, 4, 3]]

@[expose] def fourReps (_ : Unit := ()) : List (Equiv.Perm (Fin 36)) :=
  fourWords.map (evalCodes (sylGens ()))

@[expose] def x0 (_ : Unit := ()) : Equiv.Perm (Fin 36) :=
  evalCodes (sylGens ()) [1, 3, 2, 4, 1, 3, 4, 2]

@[expose] def y0 (_ : Unit := ()) : Equiv.Perm (Fin 36) :=
  evalCodes (sylGens ()) [1, 2, 4, 2, 4, 3]

@[expose] def candWords : List (List ℤ) :=
  [[2, 1, 2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1, 2, 2, 1, -2, -2, -2, -1, -2, -1,
    -2, -1, 2, 2, -1, 2, -1, -2, -2, -1, 2, 2, 1, -2, -2, -2, 1, -2, -2, -2, 1, 2, 2, -1, -2, -2,
    -2], [], [1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -2, -1, 2, 2, 1, 2, 2, 2, 1, -2, -2, 1,
    -2, -2, 1, 2, 1, -2, -2], [-2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, -2, 1, -2, 1, -2, -2,
    1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, -2, -2, -2, 1, -2, -2, -2, 1, -2, -2, -2, 1, 2, 2, 1, 2]]

@[expose] def candPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 36)) :=
  candWords.map (evalCodes sp6Gens)

@[expose] def perRep : List (List ℕ) :=
  [[0], [0, 1], [], [], [0], [], [0, 2], [2], [], [], [0, 2], [0, 3], [], [], [], [], [], [], [],
    [], [], [], [], [], []]

@[expose] def repCands (_ : Unit := ()) : List (List (Table × Table)) :=
  let T := ((candPerms ()).map fun g => (toTable g, toTable g⁻¹)).toArray
  let d := (toTable (1 : Equiv.Perm (Fin 36)), toTable (1 : Equiv.Perm (Fin 36)))
  perRep.map fun l => l.map fun i => T.getD i d

@[expose] def sp6TwinSylow (_ : Unit := ()) : Bool :=
  let Q := sylQ ()
  Q.check && Q.orderCertificate == 512

@[expose] def sp6TwinReps (_ : Unit := ()) : Bool :=
  let gs := sylGens ()
  let R := (fourReps ()).map toTable
  repsOK 36 (listTables gs) (listTables (gs.map (·⁻¹))) (cosetOrderTables (sylQ ()) 1 4) R
      4000 &&
    R.all (ordTest 36 4)

@[expose] def sp6TwinK0 (_ : Unit := ()) : Bool :=
  let x := x0 ()
  let y := y0 ()
  q8RelT 36 (toTable x) (toTable x⁻¹) (toTable y) (toTable y⁻¹)

@[expose] def sp6TwinPairs (_ : Unit := ()) : Bool :=
  let x := x0 ()
  let y := y0 ()
  pairsOK 36 (spanT 36 (toTable x) (toTable x⁻¹) (toTable y) (toTable y⁻¹))
    (cosetOrderTables (sylQ ()) 1 4) ((fourReps ()).map toTable) (repCands ())

end Certificates.S7TwinSp6
