module

public import CFSG.Sporadic.Schreier.LyCheckOrbit

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

abbrev Mat := Array (Array Nat)

@[inline, expose] def letterM (g gi : Nat → Mat) (l : Int) : Mat :=
  if 0 < l then g (l.toNat - 1) else gi ((-l).toNat - 1)

@[expose] def wordFromM (g gi : Nat → Mat) (X : Mat) (w : List Int) : Mat :=
  w.foldl (fun X l => mulM 5 111 X (letterM g gi l)) X

@[expose] def evalWordM (g gi : Nat → Mat) (w : List Int) : Mat := wordFromM g gi (idM 111) w

@[expose] def seedM (k : Nat) : Mat := if k = 0 then matA else matB

@[expose] def seedMInv (b4 : Mat) (k : Nat) : Mat := if k = 0 then matA else b4

@[inline, expose] def pairAt (cs : Array (Mat × Mat)) (j : Nat) : Mat × Mat :=
  cs.getD j (idM 111, idM 111)

@[expose] def extendM (start : Array (Mat × Mat)) (ws : List (List Int)) : Array (Mat × Mat) :=
  ws.foldl (fun acc w =>
    let X := evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w
    acc.push (X, invM 5 111 X)) start

@[expose] def cStarArr (b4 : Mat) : Array (Mat × Mat) :=
  let c0 := evalWordM seedM (seedMInv b4) seedWord0
  let c1 := evalWordM seedM (seedMInv b4) seedWord1
  extendM #[(c0, invM 5 111 c0), (c1, invM 5 111 c1)] cDerivations.toList

@[expose] def diffMod5 (X Y : Mat) : Bool :=
  (List.range 111).any fun r => (List.range 111).any fun c => X[r]![c]! % 5 != Y[r]![c]! % 5

@[expose] def invPairsOK (cs : Array (Mat × Mat)) : Bool :=
  cs.all fun p => mulM 5 111 p.1 p.2 == idM 111

@[expose] def twWord (i x : Nat) : List Nat :=
  match chainTransversals.toList.find? (fun t => t.1 = i ∧ t.2.1 = x) with
  | some t => t.2.2
  | none => []

@[expose] def id11 : Array Nat := Array.ofFn (n := 11) fun x => x.val

@[expose] def compP (P Q : Array Nat) : Array Nat := Array.ofFn (n := 11) fun x => P[Q[x.val]!]!

@[inline, expose] def pArr (j : Nat) : Array Nat := cPerms[j]!

@[expose] def tPArr (i x : Nat) : Array Nat := (twWord i x).foldl (fun P j => compP P (pArr j)) id11

@[expose] def transTab (cs : Array (Mat × Mat)) : Array (Array (Mat × Mat)) :=
  Array.ofFn (n := 11) fun i => Array.ofFn (n := 11) fun x =>
    ((twWord i.val x.val).foldl (fun X j => mulM 5 111 X (pairAt cs j).1) (idM 111),
      (twWord i.val x.val).reverse.foldl (fun X j => mulM 5 111 X (pairAt cs j).2) (idM 111))

@[inline, expose] def tabAt (T : Array (Array (Mat × Mat))) (i x : Nat) : Mat × Mat :=
  (T.getD i #[]).getD x (idM 111, idM 111)

end CFSG.Sporadic.LySchreier.Native

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

@[expose] def carWordsL : List (List Int) :=
  [[2, 2, 12, -2, -2], [2, 4, -12, -4, -2], [2, 7, -12, -8, -2], [3, -2, -8, -11, 2, -3],
    [-1, 3, -11, -12, -3, 1], [-4, -2, 12, 2, 4], [4, -1, 11, 1, -4], [-1, 3, -11, -3, 1],
    [4, -2, 12, 2, -4]]

@[expose] def carWords (i : Fin 9) : List Int := carWordsL.getD i.val []

@[expose] def carGenWords (k : Fin 2) : List (Fin 9) :=
  [[5, 5, 2, 3, 3, 8, 0, 0, 7], [1, 1, 4, 5, 5, 4, 6, 7, 7, 2, 3, 3, 0, 8]].getD k.val []

@[expose] def carMat (cs : Array (Mat × Mat)) (i : Fin 9) : Mat :=
  evalWordM (fun j => (pairAt cs j).1) (fun j => (pairAt cs j).2) (carWords i)

@[expose] def oneOrA (X : Mat) : Bool := X == idM 111 || X == Ly.Native.matA

@[expose] def carFoldM (g : Fin 9 → Mat) (w : List (Fin 9)) : Mat :=
  w.foldl (fun X n => mulM 5 111 X (g n)) (idM 111)

@[expose] def carPresOK (cs : Array (Mat × Mat)) : Bool :=
  (List.finRange 9).all (fun i => oneOrA (mulM 5 111 (mulM 5 111 (carMat cs i) (carMat cs i))
    (carMat cs i))) &&
  (List.finRange 9).all (fun i => (List.finRange 9).all fun j => !decide (i < j) ||
    oneOrA (mulM 5 111 (mulM 5 111 (carMat cs i) (carMat cs j))
      (mulM 5 111 (carMat cs i) (carMat cs j)))) &&
  (List.finRange 2).all (fun k => carFoldM (carMat cs) (carGenWords k) == (pairAt cs k).1 ||
    carFoldM (carMat cs) (carGenWords k) == mulM 5 111 (pairAt cs k).1 Ly.Native.matA) &&
  mulM 5 111 (mulM 5 111 (carMat cs 0) (carMat cs 1)) (mulM 5 111 (carMat cs 0) (carMat cs 1)) ==
    Ly.Native.matA

end CFSG.Sporadic.LySchreier

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native

@[expose] def coverCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  let cs := cStarArr b4
  mulM 5 111 matB b4 == idM 111 && cs.size == 12 && invPairsOK cs &&
    mulM 5 111 matA (pairAt cs 0).1 == mulM 5 111 (pairAt cs 0).1 matA &&
    mulM 5 111 matA (pairAt cs 1).1 == mulM 5 111 (pairAt cs 1).1 matA &&
    diffMod5 (pairAt cs 0).1 (idM 111) && diffMod5 (pairAt cs 0).1 matA && carPresOK cs

end CFSG.Sporadic.LySchreier.Native
