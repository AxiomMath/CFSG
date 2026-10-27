module

public import Certificates.Data.CFSGNative.MonsterB.Max2TowerData
public import Certificates.Data.CFSGNative.MonsterVis.Act

public section

namespace CFSG.Monster.B.Max2.Native

open CFSG.Monster.VisCert.Native (actGo)

@[inline, expose] def hexVal (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

@[expose] def hexAt (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => hexAt b o w * 16 + hexVal (b.get! (o + w))

@[expose] def towerDag (_ : Unit) : Array (Int × Nat) :=
  let b := dagHex.toUTF8
  Array.ofFn (n := dagSize) fun j => ((hexAt b (8 * j.val) 4 : Int) - 4, hexAt b (8 * j.val + 4) 4)

@[expose] def towerPointsAll (_ : Unit) : Array (Nat × Nat) :=
  let b := pointsHex.toUTF8
  Array.ofFn (n := levelOffsets[6]!) fun k => (hexAt b (10 * k.val) 6, hexAt b (10 * k.val + 6) 4)

@[expose] def act22 (rows : Array Nat) (v : Nat) : Nat := actGo rows v 22 0

@[expose] def id22 (_ : Unit := ()) : Array Nat := (Array.range 22).map (1 <<< ·)

@[expose] def mul22 (A B : Array Nat) : Array Nat := (Array.range 22).map fun i => act22 B A[i]!

@[expose] def inv22 (rows : Array Nat) : Array Nat := Id.run do
  let mut A : Array (Nat × Nat) := (Array.range 22).map fun i => (rows[i]!, 1 <<< i)
  for c in [0:22] do
    let mut p := 22
    for r in [c:22] do
      if p == 22 && (A[r]!.1.testBit c) then p := r
    if p < 22 then
      let tmp := A[c]!
      A := (A.set! c A[p]!).set! p tmp
      for r in [0:22] do
        if r != c && (A[r]!.1.testBit c) then
          A := A.set! r (A[r]!.1 ^^^ A[c]!.1, A[r]!.2 ^^^ A[c]!.2)
  return A.map (·.2)

@[expose] def nodeStep (acc : Array (Array Nat)) (e : Int × Nat) : Array (Array Nat) :=
  if e.1 = -2 then acc.push id22
  else if e.1 = -3 then acc.push r1Rows
  else if e.1 = -4 then acc.push r2Rows
  else if e.1 = -1 then acc.push (inv22 acc[e.2]!)
  else acc.push (mul22 acc[e.1.toNat]! acc[e.2]!)

@[expose] def nodeMats (_ : Unit) : Array (Array Nat) := (towerDag ()).foldl nodeStep #[]

@[expose] def eq22 (A B : Array Nat) : Bool :=
  A.size == 22 && B.size == 22 && (List.range 22).all fun i => A[i]! == B[i]!

@[expose] def wf22 (A : Array Nat) : Bool := A.size == 22 && A.all (· < 2 ^ 22)

@[expose] def nodeOK (D : Array (Int × Nat)) (N : Array (Array Nat)) (j : Nat) : Bool :=
  let e := D[j]!
  if e.1 = -2 then eq22 N[j]! id22
  else if e.1 = -3 then eq22 N[j]! r1Rows
  else if e.1 = -4 then eq22 N[j]! r2Rows
  else if e.1 = -1 then decide (e.2 < j) && eq22 (mul22 N[e.2]! N[j]!) id22
  else decide (0 ≤ e.1) && decide (e.1.toNat < j) && decide (e.2 < j) &&
    eq22 N[j]! (mul22 N[e.1.toNat]! N[e.2]!)

@[expose] def levelPoints (P : Array (Nat × Nat)) (i : Nat) : List (Nat × Nat) :=
  (List.range (levelOffsets[i + 1]! - levelOffsets[i]!)).map fun k => P[levelOffsets[i]! + k]!

@[expose] def levelOK (P : Array (Nat × Nat)) (N : Array (Array Nat)) (i : Nat) : Bool :=
  let b := towerLevels[i]!.1
  let pts := levelPoints P i
  pts.length == towerLevels[i]!.2 && decide (b < 2 ^ 22) &&
  decide ((pts.map (·.1)).Nodup) &&
  pts.all fun p => decide (p.1 < 2 ^ 22) && decide (p.2 < N.size) && act22 N[p.2]! b == p.1 &&
    (List.range i).all fun k => act22 N[p.2]! towerLevels[k]!.1 == towerLevels[k]!.1

@[expose] def sizesOK (_ : Unit := ()) : Bool := (nodeMats ()).size == dagSize && (towerDag ()).size == dagSize

@[expose] def gensOK (_ : Unit := ()) : Bool :=
  eq22 (mul22 r1Rows (inv22 r1Rows)) id22 && eq22 (mul22 (inv22 r1Rows) r1Rows) id22 &&
  eq22 (mul22 r2Rows (inv22 r2Rows)) id22 && eq22 (mul22 (inv22 r2Rows) r2Rows) id22

@[expose] def nodesOK (_ : Unit := ()) : Bool := (List.range dagSize).all (nodeOK (towerDag ()) (nodeMats ()))

@[expose] def levelsOK (_ : Unit := ()) : Bool := (List.range 6).all (levelOK (towerPointsAll ()) (nodeMats ()))

@[expose] def shapeOK (_ : Unit := ()) : Bool :=
  towerLevels.size == 6 && levelOffsets.size == 7 &&
  towerLevels.toList.map (·.2) == [2300, 1408, 840, 216, 36, 2]

@[expose] def towerCheck (_ : Unit := ()) : Bool := sizesOK && gensOK && nodesOK && levelsOK && shapeOK

end CFSG.Monster.B.Max2.Native
