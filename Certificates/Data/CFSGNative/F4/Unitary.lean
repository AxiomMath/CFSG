module

public import Certificates.Data.CFSGNative.F4.Basic
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.F4.Native

open CFSG.Sporadic.Th.Native

@[expose] def scaleC (a c : Nat) : Nat :=
  (List.range 6).foldl (fun acc i => acc + f4mul a (coord c i) * 4 ^ i) 0

@[expose] def leadC (c : Nat) : Nat :=
  (List.range 6).foldr (fun i acc => if coord c i != 0 then coord c i else acc) 0

@[expose] def normC (c : Nat) : Nat := let a := leadC c; scaleC (f4mul a a) c

@[inline, expose] def addC (c d : Nat) : Nat := c ^^^ d

@[expose] def tvC (v x : Nat) : Nat := addC x (scaleC (hermC x v) v)

@[expose] def uPts (_ : Unit := ()) : Array Nat :=
  ((List.range 4096).filter fun c => c != 0 && hermC c c == 0 && normC c == c).toArray

@[expose] def uPos (_ : Unit := ()) : Array Nat := Array.ofFn (n := 4096) fun c => uPts.toList.idxOf c.val

@[expose] def tvTable (v : Nat) : Table :=
  Array.ofFn (n := 693) fun k => UInt32.ofNat (uPos[normC (tvC v uPts[k.val]!)]!)

@[expose] def weightC (c : Nat) : Nat := ((List.range 6).filter fun i => coord c i != 0).length

@[expose] def tvGens (_ : Unit := ()) : Array Nat :=
  (uPts.filter fun c => weightC c == 2).push (1 + 4 + 16 + 64)

@[expose] def uPtsOK (_ : Unit := ()) : Bool :=
  uPts.size == 693 && tvGens.size == 46 &&
    (List.range 692).all (fun i => uPts[i]! < uPts[i + 1]!) &&
    (List.range 4096).all (fun c => c == 0 || hermC c c != 0 || uPts.contains (normC c)) &&
    tvGens.all (fun v => uPts.contains v)

end CFSG.F4.Native
