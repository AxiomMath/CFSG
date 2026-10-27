module

public import CFSG.Sporadic.HNSchreier.OrbitCheck
public import CFSG.Sporadic.HNSchreier.SeedsCheck
public import Std.Data.HashMap
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.F5.Native CFSG.Sporadic.He.Native

@[expose] def rowsM : Array (Array Nat) := rowsOf 5 133 Data.formPayload

@[expose] def formChecks (A B M : Array (Array Nat)) : Bool :=
  colsMat 133 M == M && mulM 5 133 M (invM 5 133 M) == idM 133 &&
    mulM 5 133 (mulM 5 133 (colsMat 133 A) M) A == M &&
    mulM 5 133 (mulM 5 133 (colsMat 133 B) M) B == M

@[expose] def sigRows (O : VOrbit) (M : Array (Array Nat)) (base : List Nat) :
    Array (Array Nat) :=
  (base.map fun b => mulVec 5 133 M (bytesToNats O.keys[b]!)).toArray

@[noinline, expose] def sigsOf (O : VOrbit) (T : Array W17) (n : Nat) : Array ByteArray :=
  Array.ofFn (n := n) fun i => mulW 22 133 T O.keys[i.val]!

@[noinline, expose] def keyIndex (S : Array ByteArray) : Std.HashMap ByteArray Nat :=
  Nat.fold S.size (fun i _ m => m.insert S[i]! i) {}

@[expose] def keysDistinct (S : Array ByteArray) (idx : Std.HashMap ByteArray Nat) : Bool :=
  (List.range S.size).all fun i => idx.getD S[i]! S.size == i

@[noinline, expose] def sigChecks (O : VOrbit) : Bool :=
  let S := sigsOf O (frTable 22 133 (sigRows O rowsM Data.baseList)) hnsData.n
  S.size == hnsData.n && keysDistinct S (keyIndex S)

end CFSG.Sporadic.HNSchreier.Native
