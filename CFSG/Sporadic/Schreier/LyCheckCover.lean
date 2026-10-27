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

@[expose] def invP (P : Array Nat) : Array Nat :=
  Array.ofFn (n := 11) fun y => ((List.range 11).find? fun x => P[x]! == y.val).getD 0

@[inline, expose] def pArr (j : Nat) : Array Nat := cPerms[j]!

@[expose] def tPArr (i x : Nat) : Array Nat := (twWord i x).foldl (fun P j => compP P (pArr j)) id11

@[expose] def fixesBelow (j i : Nat) : Bool := allIn 0 i fun l => (pArr j)[l]! == l

@[expose] def transTab (cs : Array (Mat × Mat)) : Array (Array (Mat × Mat)) :=
  Array.ofFn (n := 11) fun i => Array.ofFn (n := 11) fun x =>
    ((twWord i.val x.val).foldl (fun X j => mulM 5 111 X (pairAt cs j).1) (idM 111),
      (twWord i.val x.val).reverse.foldl (fun X j => mulM 5 111 X (pairAt cs j).2) (idM 111))

@[inline, expose] def tabAt (T : Array (Array (Mat × Mat))) (i x : Nat) : Mat × Mat :=
  (T.getD i #[]).getD x (idM 111, idM 111)

@[expose] def stripStep (T : Array (Array (Mat × Mat))) (st : Array Nat × Mat) (l : Nat) :
    Array Nat × Mat :=
  let y := st.1[l]!
  (compP (invP (tPArr l y)) st.1, mulM 5 111 (tabAt T l y).2 st.2)

@[expose] def relResidue (cs : Array (Mat × Mat)) (T : Array (Array (Mat × Mat)))
    (i x j : Nat) : Array Nat × Mat :=
  let y := (pArr j)[x]!
  let P0 := compP (invP (tPArr i y)) (compP (pArr j) (tPArr i x))
  let X0 := mulM 5 111 (tabAt T i y).2 (mulM 5 111 (pairAt cs j).1 (tabAt T i x).1)
  ((List.range 11).filter fun l => decide (i < l)).foldl (stripStep T) (P0, X0)

@[expose] def relOK (cs : Array (Mat × Mat)) (T : Array (Array (Mat × Mat))) : Bool :=
  allIn 0 11 fun i => (chainOrbits[i]!).all fun x => allIn 0 12 fun j =>
    !fixesBelow j i || (let r := relResidue cs T i x j
      r.1 == id11 && (r.2 == idM 111 || r.2 == matA))

@[expose] def transInvOK : Bool :=
  allIn 0 11 fun i => allIn 0 11 fun x =>
    compP (tPArr i x) (invP (tPArr i x)) == id11 && (invP (tPArr i x)).all (· < 11)

@[expose] def coverCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  let cs := cStarArr b4
  let T := transTab cs
  mulM 5 111 matB b4 == idM 111 && cs.size == 12 && invPairsOK cs &&
    mulM 5 111 matA (pairAt cs 0).1 == mulM 5 111 (pairAt cs 0).1 matA &&
    mulM 5 111 matA (pairAt cs 1).1 == mulM 5 111 (pairAt cs 1).1 matA &&
    diffMod5 (pairAt cs 0).1 (idM 111) && diffMod5 (pairAt cs 0).1 matA && transInvOK &&
    relOK cs T &&
    (relResidue cs T 0 1 0).2 == matA

end CFSG.Sporadic.LySchreier.Native
