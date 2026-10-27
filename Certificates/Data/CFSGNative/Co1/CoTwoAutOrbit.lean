module

public import Certificates.Data.CFSGNative.Co1.CoTwoChain

public section

namespace CFSG.Sporadic.Co1.CoTwoAutNative

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoNative
  CFSG.Sporadic.SmallF2.Native

@[expose] def uncovered (Ft ptsO : Array Nat) (posO : Array UInt32) (nO : Nat)
    (Ts : List (OTree × Array UInt32)) (w : Nat) : Bool :=
  !bilN Ft w 2 && w != 0 && w != 2 && !inPts ptsO posO nO w && !inPts ptsO posO nO (w ^^^ 2) &&
    Ts.all fun p => !inPts p.1.pts p.2 p.1.pts.size w

@[expose] def bigCheck (rr : Nat → Array Nat) (lv roots : List Nat) (bound : Nat)
    (Ft ptsO : Array Nat) (posO : Array UInt32) (nO : Nat) : Bool :=
  let Ts := roots.map fun b => (b, orbitTreeBFS rr lv b)
  let Ps := Ts.map fun p => (p.2, posTable 24 p.2.pts)
  Ts.all (fun p => otreeOK rr lv p.1 p.2 && decide (bound < p.2.pts.size)) &&
    countBelow (uncovered Ft ptsO posO nO Ps) 16777216 0 == 0

@[expose] def adjT (Qt ptsO : Array Nat) (posO : Array UInt32) (nO : Nat) (u : Nat) : Bool :=
  (inPts ptsO posO nO u && type4N Qt ptsO posO nO (u ^^^ 2)) ||
    (type4N Qt ptsO posO nO u && inPts ptsO posO nO (u ^^^ 2))

@[expose] def maskOf (m : Nat) (l : List Nat) : Array Bool :=
  l.foldl (fun a j => a.set! j true) (Array.replicate m false)

@[expose] def graphCheck (Qt ptsO : Array Nat) (posO : Array UInt32) (nO : Nat) (vt : Array Nat)
    (nbr : Array (List Nat)) : Bool :=
  decide (vt.size = 2300) && decide (nbr.size = 2300) &&
    allIn 0 2300 (fun i => decide (vt[i]! < 2 ^ 24) && inPts ptsO posO nO vt[i]! &&
      inPts ptsO posO nO (vt[i]! ^^^ 2)) &&
    allIn 0 2300 (fun i => allIn 0 i fun j =>
      (vt[i]! ^^^ vt[j]!) != 0 && (vt[i]! ^^^ vt[j]!) != 2) &&
    allIn 0 2300 (fun i =>
      let mask := maskOf 2300 nbr[i]!
      allIn 0 2300 fun j => mask[j]! == adjT Qt ptsO posO nO (vt[i]! ^^^ vt[j]!))

end CFSG.Sporadic.Co1.CoTwoAutNative
