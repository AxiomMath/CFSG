module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterVis.FrameData
public import Certificates.Data.CFSGNative.MonsterVis.Act

public section

namespace CFSG.Monster.B.Co2.Native

open CFSG.Monster.VisCert.Native (frameRows actRows actGo)

@[expose] def actD (d : Nat) (rows : Array Nat) (v : Nat) : Nat := actGo rows v d 0

@[expose] def invMat (d : Nat) (rows : Array Nat) : Array Nat := Id.run do
  let mut A : Array (Nat × Nat) := Array.ofFn (n := d) fun i => (rows[i.val]!, 1 <<< i.val)
  for c in [0:d] do
    let mut p := d
    for r in [c:d] do
      if p == d && (A[r]!.1.testBit c) then p := r
    if p < d then
      let tmp := A[c]!
      A := (A.set! c A[p]!).set! p tmp
      for r in [0:d] do
        if r != c && (A[r]!.1.testBit c) then
          A := A.set! r (A[r]!.1 ^^^ A[c]!.1, A[r]!.2 ^^^ A[c]!.2)
  return A.map (·.2)

@[expose] def frameInv (_ : Unit := ()) : Array (Array Nat) := frameRows.map (invMat 24)

@[inline, expose] def pairLetterAct (l : Int) (x : Nat) : Nat :=
  if 0 < l then actRows frameRows[l.natAbs]! x else actRows frameInv[l.natAbs]! x

@[expose] def pairWordAct : List Int → Nat → Nat
  | [], x => x
  | l :: w, x => pairWordAct w (pairLetterAct l x)

@[expose] def frameWordAct : List Int → Nat → Nat
  | [], x => x
  | l :: w, x => frameWordAct w (actRows frameRows[l.toNat]! x)

@[expose] def recordAct (r : GenRecord) (x : Nat) : Nat :=
  match r.kind with
  | .pairStabilizer => pairWordAct r.word x
  | _ => frameWordAct r.word x

@[expose] def vSeed (_ : Unit := ()) : Nat := 12288

@[expose] def spanIdx : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 28, 30, 33, 53, 56, 57, 58, 60, 62, 257]

@[expose] def spanInv : Array Nat :=
  #[32621, 5400, 3080, 18106, 9414, 1300811, 194757, 367150, 713297, 1177802, 819865, 2160755,
    2160754, 2160763, 2161508, 2160654, 2161267, 2161011, 2161615, 2160739, 2160753, 2161281]

@[expose] def vecPos (_ : Unit := ()) : Array Nat := Id.run do
  let mut p : Array Nat := Array.replicate (2 ^ 22) 2300
  for j in [0:2300] do
    p := p.set! vectors[j]! j
  return p

@[expose] def permInv (_ : Unit := ()) : Array (Array Nat) := permutations.map (invCand deg)

@[inline, expose] def permLetter (l : Int) : Array Nat :=
  if 0 < l then permutations[l.natAbs - 1]! else permInv[l.natAbs - 1]!

@[expose] def wordPermA : List Int → Array Nat
  | [] => idA deg
  | l :: w => compA deg (wordPermA w) (permLetter l)

@[expose] def powA (t : Array Nat) : Nat → Array Nat
  | 0 => idA deg
  | e + 1 => compA deg t (powA t e)

@[expose] def matCheck (_ : Unit := ()) : Bool :=
  let n := deg
  let a := pairPerms[0]!
  let b := pairPerms[1]!
  let ab := compA n a b
  allLt 2 (fun j => allLt 24 fun i =>
      actRows frameRows[j + 1]! (frameInv[j + 1]!)[i]! == 1 <<< i) &&
    allLt 24 (fun r => allLt 24 fun k =>
      recordAct genRecords[r]! (1 <<< k) == (genRecords[r]!.matrix)[k]!) &&
    allLt 24 (fun r => actRows genRecords[r]!.matrix vSeed == vSeed) &&
    allLt 24 (fun r => allLt 22 fun t =>
      decide ((genRecords[r]!.quotientMatrix)[t]! < 2 ^ 22) &&
        ((actRows genRecords[r]!.matrix quotientBasis[t]! ^^^
            actD 22 quotientBasis (genRecords[r]!.quotientMatrix)[t]!) == 0 ||
          (actRows genRecords[r]!.matrix quotientBasis[t]! ^^^
            actD 22 quotientBasis (genRecords[r]!.quotientMatrix)[t]!) == vSeed)) &&
    allLt 2300 (fun j => decide (vectors[j]! < 2 ^ 22) && vecPos[vectors[j]!]! == j) &&
    spanIdx.size == 22 && allLt 22 (fun t => decide (spanIdx[t]! < 2300)) &&
    allLt 22 (fun t => actD 22 (spanIdx.map fun j => vectors[j]!) spanInv[t]! == 1 <<< t) &&
    allLt 24 (fun r => allLt 2300 fun j =>
      actD 22 genRecords[r]!.quotientMatrix vectors[j]! == vectors[(permutations[r]!)[j]!]!) &&
    allLt 2 (fun i => eqA n pairPerms[i]! (wordPermA pairWords[i]!)) &&
    eqA n (powA a 2) (idA n) && eqA n (powA b 5) (idA n) && eqA n (powA ab 23) (idA n) &&
    !(eqA n a (idA n)) && !(eqA n b (idA n)) && !(eqA n ab (idA n))

end CFSG.Monster.B.Co2.Native
