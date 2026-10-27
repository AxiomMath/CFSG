
module

public import CFSG.Sporadic.HNSchreier.PrimCheckBase
public import CFSG.Sporadic.HNSchreier.LocalData
public import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheckBase
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

@[expose] def natArr (p : List Nat) : Array Nat := p.toArray

@[expose] def cycle01 (i : Nat) : Array Nat :=
  Array.ofFn (n := 12) fun j => if j.val = 0 then 1 else if j.val = 1 then i else
    if j.val = i then 0 else j.val

@[expose] def seedWordIdx (a0 a1 : Array Nat) (w : List Nat) (x : Nat) : Nat :=
  w.foldr (fun l y => (if l = 1 then a0 else a1)[y]!) x

@[expose] def xIndex (hS : Array (Array Nat)) (root : Nat) (recs : List (Nat × Nat)) :
    Array Nat :=
  (recs.drop 1).foldl (fun acc r => acc.push (hS[r.2 - 1]!)[acc[r.1]!]!) #[root]

@[noinline, expose] def localChecks (n : Nat) (a0 a1 : Array Nat) : Bool :=
  let regs := progRegs n (initRegs n a0 a1) Data.subgroupProgram
  let h1 := regs[1]!
  let h2 := regs[2]!
  let hS := extendStrong n #[h1, h2] LocalData.strongWords
  let p1 := natArr LocalData.natGen1
  let p2 := natArr LocalData.natGen2
  let nS := extendStrong 12 #[p1, p2] LocalData.strongWords
  let nSi := pinvs 12 nS
  let xs := xIndex hS (seedWordIdx a0 a1 LocalData.rootWord 0) LocalData.parents
  strongOK n h1 h2 hS LocalData.strongWords && strongOK 12 p1 p2 nS LocalData.strongWords &&
    LocalData.strongImages.size == 17 &&
    allBelowN 17 (fun j => peq 12 nS[j]! (natArr LocalData.strongImages[j]!)) &&
    LocalData.tripleWords.size == 10 &&
    allBelowN 10 (fun i => plettersOK 17 LocalData.tripleWords[i]! &&
      peq 12 (pword 12 nS nSi LocalData.tripleWords[i]!) (cycle01 (i + 2))) &&
    LocalData.parents.length == 462 && xs.size == 462 &&
    xs[0]! == seedWordIdx a0 a1 LocalData.rootWord 0 &&
    allBelowN 462 (fun i => i == 0 || (decide (LocalData.parents[i]!.1 < i) &&
      (LocalData.parents[i]!.2 == 1 || LocalData.parents[i]!.2 == 2) &&
      xs[i]! == (hS[LocalData.parents[i]!.2 - 1]!)[xs[LocalData.parents[i]!.1]!]!)) &&
    allBelowN 462 (fun i => decide (xs[i]! < n)) &&
    allBelowN 462 (fun i => allBelowN 462 fun j => i == j || xs[i]! != xs[j]!) &&
    LocalData.lperm1.size == 462 && LocalData.lperm2.size == 462 &&
    allBelowN 462 (fun i => decide (LocalData.lperm1[i]! < 462) &&
      decide (LocalData.lperm2[i]! < 462) &&
      (hS[0]!)[xs[i]!]! == xs[LocalData.lperm1[i]!]! &&
      (hS[1]!)[xs[i]!]! == xs[LocalData.lperm2[i]!]!)

@[expose] def labMasks : Array Nat := LocalData.labels.map maskOfList

@[expose] def labelChecks : Bool :=
  let M := labMasks
  let p1 := natArr LocalData.natGen1
  let p2 := natArr LocalData.natGen2
  M.size == 462 && LocalData.lperm1.size == 462 && LocalData.lperm2.size == 462 &&
    allBelowN 462 (fun k => decide (M[k]! < 4096) && popc12 M[k]! == 6 && M[k]!.testBit 0) &&
    allBelowN 462 (fun k => allBelowN 462 fun k' => k == k' || M[k]! != M[k']!) &&
    allBelowN 462 (fun k => decide (LocalData.lperm1[k]! < 462) &&
      decide (LocalData.lperm2[k]! < 462) &&
      M[LocalData.lperm1[k]!]! == canonMask (permMask p1 M[k]!) &&
      M[LocalData.lperm2[k]!]! == canonMask (permMask p2 M[k]!))

@[noinline, expose] def localChecksO (O : VOrbit) : Bool :=
  localChecks hnsData.n (natTab O.alpha) (natTab O.beta)

end CFSG.Sporadic.HNSchreier.Native
