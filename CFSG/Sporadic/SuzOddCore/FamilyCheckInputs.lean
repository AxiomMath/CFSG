module

public import CFSG.Sporadic.SuzOddCore.ArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Perm.Chain
public meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native

@[expose] def famBFS (n : Nat) (idxGens setGens : Array (Array Nat)) (seed : List Nat) :
    Array (List Nat) := Id.run do
  let mut fam : Array (List Nat) := Array.replicate n []
  let mut seen : Array Bool := Array.replicate n false
  fam := fam.set! 0 seed
  seen := seen.set! 0 true
  let mut queue : Array Nat := #[0]
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let d := queue[head]!
      head := head + 1
      for k in [0:idxGens.size] do
        let e := (idxGens[k]!)[d]!
        if !seen[e]! then
          seen := seen.set! e true
          fam := fam.set! e (imgSorted setGens[k]! fam[d]!)
          queue := queue.push e
  return fam

@[expose] def famOK (n m : Nat) (idxGens setGens : Array (Array Nat)) (fam : Array (List Nat)) :
    Bool :=
  fam.size == n && idxGens.size == setGens.size &&
    allLt n (fun d => (fam[d]!).all (fun y => decide (y < m)) && strictIncr fam[d]!) &&
    allLt idxGens.size (fun k => allLt n fun d =>
      decide ((idxGens[k]!)[d]! < n) && fam[(idxGens[k]!)[d]!]! == imgSorted setGens[k]! fam[d]!) &&
    allLt n (fun d => d == 0 || fam[d]! != fam[0]!)

@[expose] def suzFam : Array (List Nat) :=
  famBFS 1782 #[b0Arr, b1Arr] #[certArr 0, certArr 1] familySeed

@[expose] def smallLetters : Array Table :=
  #[b0Arr.map UInt32.ofNat, (invCand 1782 b0Arr).map UInt32.ofNat, b1Arr.map UInt32.ofNat,
    (invCand 1782 b1Arr).map UInt32.ofNat]

@[expose] def smallTree : CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.treeBFS 1782 0 smallLetters #[0, 1, 2, 3]

@[expose] def smallTreeOK : Bool :=
  CFSG.Perm.Native.treeOK 1782 0 smallTree smallLetters #[0, 1, 2, 3] &&
    smallTree.pts.size == 1782

end CFSG.Sporadic.SuzOddCore
