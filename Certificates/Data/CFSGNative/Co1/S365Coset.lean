module

public import Certificates.Data.CFSGNative.Co1.Involutions
public import Std.Data.HashSet

public section

namespace CFSG.Sporadic.Co1.S365Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

@[expose] def parity24N (x : Nat) : Bool :=
  (List.range 24).foldl (fun acc j => acc ^^ x.testBit j) false

@[expose] def inPtsN (pts : Array Nat) (pos : Array UInt32) (n w : Nat) : Bool :=
  decide ((pos[w]!).toNat < n) && pts[(pos[w]!).toNat]! == w

@[expose] def tyLabN (qr pts : Array Nat) (pos : Array UInt32) (n w : Nat) : Nat :=
  if w = 0 then 0 else if parity24N (vecMulN 24 qr w &&& w) then 2
  else if inPtsN pts pos n w then 3 else 1

@[expose] def canon4 (x y v : Nat) : Nat := min (min v (v ^^^ x)) (min (v ^^^ y) (v ^^^ x ^^^ y))

@[expose] def cosetBFS (Mts : Array (Array Nat)) (x y c0 cap : Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut vis : Array UInt8 := Array.replicate (1 <<< 24) 0
  let mut pts : Array Nat := #[c0]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  vis := vis.set! c0 1
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      for l in [0:Mts.size] do
        let w := canon4 x y (vecMulN 24 Mts[l]! v)
        if vis[w]! == 0 then
          vis := vis.set! w 1
          pts := pts.push w
          par := par.push h
          lab := lab.push l
    else break
  return (pts, par, lab)

@[expose] def coverBad4 (qr pts : Array Nat) (pos : Array UInt32) (n x y : Nat) (inL : Nat → Bool)
    (v : Nat) : Bool :=
  tyLabN qr pts pos n v == 1 && tyLabN qr pts pos n (v ^^^ x) == 1 &&
    tyLabN qr pts pos n (v ^^^ y) == 1 && tyLabN qr pts pos n (v ^^^ x ^^^ y) == 1 &&
    !inL (canon4 x y v)

@[expose] def coverCheckN (qr pts : Array Nat) (pos : Array UInt32) (n x y : Nat)
    (L : Array Nat) : Bool :=
  let S : Std.HashSet Nat := Std.HashSet.ofList L.toList
  countBelow (coverBad4 qr pts pos n x y (fun u => S.contains u)) 16777216 0 == 0

end CFSG.Sporadic.Co1.S365Native
