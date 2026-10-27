module

public import Certificates.Data.AE6ModelSmall
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses

public section

namespace Certificates.AE6Model

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Th.Native Certificates.S7Twin

@[expose] def qRepWords (_ : Unit := ()) : List (List ℤ) :=
  parseWords
    "4;2,3,2,4,2,3,2,4;2,4,2,4;2,3,2,3;3,2,3,4,2,4;3;3,4;2;3,2,4,2,3,2,4;1,2,4,2,1,3,2,4,2,3,4;1,2,
     3,2,1,3,4,2,3,2,4;3,2,1,2,3,4,2,1,3,4,2,4;1,2,3,2,4,2,3,2,1,2,3,2,4,2,3,2;1,2,3,2,4,2,3,2,1,2,
     4,2;1,2,4,2,3,2,4,2,1,2,3,2;1,2,3,2,1,4,2,1,2,3,2,1,4,2;1,2,4,2,1,2,4,2;1,2,4,2,1,3,2,4,2,3;1,
     2,4,2,1,2,4;1,2,4,2,1,3,2,4,2,3,2;1;1,4;1,3;1,3,4;1,3,2,1,2,3,4,2,1,2,4;1,3,4,2,1,4,2,3,2,1,4,
     2;1,3,2,1,3,2,4,2,1,3,2,4;1,2,1,2;1,2,1,4,2,4;1,2,1,3,2,3;1,2,1,2,3,2,3,4,2,4;1,2,1,2,3,2,3;1,
     2,1,3,2,3,4,2,4;2,1,2,3,2,4,2,1,2,4,2,3;1,3,2,1,2,4,2,1,2,3,2,1,4,2;1,4,2,1,2,3,2,1,2,4,2,1,3,
     2;2,1,4,2,3,2,4,2,1,2,3;3,2,1,2,4,2,3,2,1,2,4;1,2,3,2,1,2,3,2;1,2,3,2,1,4,2,3,2,4;3,2,1,2,3,4,
     2,1,2,4;1,3,2,1,4,2,1,3,2,1,4,2"

@[expose] def qReps (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let S := sGens ()
  z0 () :: (qRepWords ()).map (evalCodes S)

@[expose] def qCutWords : List (List (List ℤ)) :=
  [[], [[4, 3, -1, -2, -1, -3, -4, 6, 4, 3, 5, 2, 1, 7]], [], [], [], [], [], [], [], [], [], [],
   [[2, 4, 2], [6, 4, 6]], [], [], [],
   [[-1, -3, -7, -3, -2, -1, -4, -3, -5, -6, -5, 3, 4, 3, 1, 2, 1, -3, -4, -3]], [], [], [], [],
   [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [[-2, -4, -8, -1, -4, -3, -5, -1, -2, -1, -3, -4, -3]], [], [], []]

@[expose] def qConjWords : List (List (List ℤ)) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
   [[], [3, 4, 2, 4, 2, 1, 6, 5, 4, 2, 1, 3, 7, 8, 3, 1, 2, 5, 6, 4, 8, 7, 5, 4, 5, 3, 4, -1, -3,
    6, 5, 3, 5, 1, 2, 8, 7, 3, 5, 1], [3, 4, 2, 4, 2, 1, 6, 5, 4, 2, 1, 3, 7, 8, 3, 1, 2, 5, 6, 4,
    8, 7, 5, 4, 5, 3, 4, 2, 1, 6, 5, 3, 1, 8, 7, 3, 4, 3], [4, -1, -3, 5, 3, 4, 1, 7, 3, 5], [-5,
    -3, -7, -2, -1, -4, -3, -5, -1, -3, -1, -4, -2, -3]]]

@[expose] def sTabs (_ : Unit := ()) : Array Table := ((sGens ()).map toTable).toArray

@[expose] def sInvTabs (_ : Unit := ()) : Array Table :=
  ((sGens ()).map fun g => toTable g⁻¹).toArray

@[expose] def repCheck (ST : List Table) (G : List (Equiv.Perm (Fin 360)))
    (r : Equiv.Perm (Fin 360)) (cw kw : List (List ℤ)) : Bool :=
  let Rt := toTable r
  let H := cw.map fun w => let h := evalCodes G w; (toTable h, toTable h⁻¹)
  let CT := kw.map fun w => let c := evalCodes G w; (toTable c, toTable c⁻¹)
  let X4 := ST.filter fun X =>
    tblEq 360 (compT 360 X X) Rt && H.all fun h => memT 360 ST (conjT 360 h.2 h.1 X)
  H.all (fun h => commT 360 h.1 Rt) && CT.all (fun c => commT 360 c.1 Rt) &&
    X4.all fun X => X4.all fun Y =>
      !tblEq 360 (compT 360 (compT 360 X Y) X) Y ||
        decide (5 ≤ (newPos (conjData CT X Y)).length)

@[expose] def q8Cover (_ : Unit := ()) : Bool :=
  let R := (qReps ()).map toTable
  repsOK 360 (sTabs ()) (sInvTabs ()) (cosetOrderTables (sQ ()) 1 2) R 100 &&
    R.all (ordTest 360 2) && memT 360 (allTables (sQ ())) (toTable (z0 ()))

@[expose] def q8Pairs (_ : Unit := ()) : Bool :=
  let ST := allTables (sQ ())
  let G := curtisPerms ()
  let R := (qReps ()).tail
  R.length == 42 && qCutWords.length == 42 && qConjWords.length == 42 &&
    (List.range 42).all fun k =>
      repCheck ST G (R.getD k 1) (qCutWords.getD k []) (qConjWords.getD k [])

end Certificates.AE6Model
