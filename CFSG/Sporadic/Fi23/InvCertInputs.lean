module

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def wordsA : Array (List Int) := #[[1], [1, 2]]

@[expose] def wordsB : Array (List Int) := #[
  [1, 2, 1, 2, 1, -2], [2, 1, 2], [1, 2, 1, 2, 1, -2, 1, -2], [2, 1, -2, 1, 2],
  [2, 1, 2, 1, -2, 1, 2], [-2, 1, 2, 1, 2, 1, -2], [2, 1, -2, 1, -2, 1, 2], [1, 2, 1, 2, 1, 2],
  [1, 2, 1, -2, 1, 2], [1, 2, 1, 2, 1, 2, 1, 2]]

@[expose] def wordsC : Array (List Int) := #[
  [-2, 1, 2, 1, 2, 1, 2], [-2, 1, 2, 1, 2, 1, -2, 1, 2, 1], [-2, 1, -2, 1, -2, 1, 2, 1],
  [2, 1, 2, 1, -2, 1, -2, 1], [1, -2, 1, 2, 1, 2, 1, 2], [1, 2, 1, -2, 1, 2, 1, 2],
  [1, 2, 1, -2], [1, 2, 1, 2, 1, 2, 1, -2, 1, 2], [1, -2, 1, -2],
  [2, 1, -2, 1, -2, 1, 2, 1, -2, 1], [1, 2, 1, -2, 1, 2, 1, -2],
  [1, 2, 1, -2, 1, 2, 1, 2, 1, -2], [1, -2, 1, 2, 1, -2, 1, 2, 1, -2], [1, -2, 1],
  [1, 2, 1, 2, 1, 2, 1, -2], [1, -2], [1, 2, 1, 2]]

@[expose] def conjsOf (O : WOrbit) (X : Table) (ws : Array (List Int)) :
    Array (Table × Table × Table) :=
  ws.map fun w =>
    let W := wordT 31671 (genTables O) w
    let Wi := invT 31671 W
    (W, Wi, compT 31671 W (compT 31671 X Wi))

@[expose] def iterPR (P R : Table) (m x : Nat) : Nat := Nat.repeat (fun y => ap P (ap R y)) m x

@[expose] def fixQ (P R : Table) (m : Nat) : Bool := chainQ.all fun q => iterPR P R m q == q

@[expose] def cycLen (P R : Table) (q : Nat) : Nat := Id.run do
  let mut x := ap P (ap R q)
  for l in [1:121] do
    if x == q then return l
    x := ap P (ap R x)
  return 0

@[expose] def oddOrd (P R : Table) : Nat := Id.run do
  let mut L := 1
  for q in chainQ do
    let c := cycLen P R q
    if c % 2 == 0 then return 0
    L := Nat.lcm L c
  return L

@[expose] def oddOK (P R : Table) : Bool :=
  let m := oddOrd P R
  m % 2 == 1 && fixQ P R m

@[expose] def coverLeaf (RA RB RC : Array (Table × Table × Table)) (P : Table) : Bool :=
  isIdT P || RC.any (fun W => oddOK P W.2.2) || RB.any (fun W => oddOK P W.2.2) ||
    RA.any (fun W => oddOK P W.2.2)

@[expose] def coverPair (RA RB RC : Array (Table × Table × Table)) (A B : Table) : Bool :=
  !invo2OK 31671 A B || coverLeaf RA RB RC (compT 31671 A B)

@[expose] def fixCount (P : Table) : Nat := (List.range 31671).countP fun i => ap P i == i

@[expose] def invChecks (O : WOrbit) (chunks : Nat) : Bool :=
  let LJ := chainLetters O
  let L := sylLetters LJ
  let T := chainTrees 31671 L sylBase
  let t0 := treeTabs 31671 T[0]! L
  let t1 := treeTabs 31671 T[1]! L
  let D := dTab O
  let bi := genTables O (-2)
  let D1 := treeActTab O D bi 1
  let C := treeActTab O D bi 39
  let XB := compT 31671 D D1
  let XC := compT 31671 XB C
  let RA := conjsOf O D wordsA
  let RB := conjsOf O XB wordsB
  let RC := conjsOf O XC wordsC
  ap D 39 == 39 && ap D1 39 == 39 && fixCount D == 3511 && fixCount XB == 695 &&
    fixCount XC == 183 && !isIdT XC &&
    RA.all (fun W => invOK 31671 W.1 W.2.1) && RB.all (fun W => invOK 31671 W.1 W.2.1) &&
    RC.all (fun W => invOK 31671 W.1 W.2.1) &&
    allIn 0 31671 (fun k => k == 0 || k == 1 || ap D k != k || ap D1 k != k ||
      fixCount (compT 31671 XB (treeActTab O D bi k)) == 183) &&
    parAll t0.size chunks fun k => t1.all fun B => coverPair RA RB RC t0[k]! B

@[expose] def invCertificate (chunks : Nat) : Bool := invChecks (orbitData ()) chunks

end CFSG.Sporadic.Fi23.Native

namespace CFSG.Sporadic.Fi23

open Native

end CFSG.Sporadic.Fi23
