module

public import Certificates.Data.CFSGNative.HN.F5Orbit

public section
namespace CFSG.Sporadic.HNSchreier.Native

inductive OrbitNats where
  | leaf (width count bits : Nat)
  | branch (leftSize : Nat) (left right : OrbitNats)

namespace OrbitNats

@[expose] def values : OrbitNats → List Nat
  | .leaf width count bits => List.ofFn (n := count) fun i =>
      (bits >>> (width * i.val)) % 2 ^ width
  | .branch _ a b => a.values ++ b.values

@[expose] def get : OrbitNats → Nat → Nat
  | .leaf width count bits, i =>
      if i < count then (bits >>> (width * i)) % 2 ^ width else 0
  | .branch leftSize a b, i => if i < leftSize then a.get i else b.get (i-leftSize)

end OrbitNats

@[expose] def orbitVector (d code : Nat) : ByteArray :=
  ⟨(List.ofFn (n := d) fun i => UInt8.ofNat ((code >>> (3*i.val)) % 8)).toArray⟩

structure PackedOrbitData where
  dimension : Nat
  vectors : OrbitNats
  alpha : OrbitNats
  beta : OrbitNats
  parents : OrbitNats
  labels : OrbitNats

@[expose] def PackedOrbitData.toOrbit (D : PackedOrbitData) : CFSG.Sporadic.F5.Native.VOrbit :=
  let keys := (D.vectors.values.map (orbitVector D.dimension)).toArray
  let index := keys.toList.zipIdx.foldl
    (fun m (v, i) => m.insert v i) (Std.HashMap.emptyWithCapacity keys.size)
  ⟨keys, (D.alpha.values.map UInt32.ofNat).toArray,
    (D.beta.values.map UInt32.ofNat).toArray,
    (D.parents.values.map UInt32.ofNat).toArray,
    (D.labels.values.map UInt32.ofNat).toArray, index⟩

end CFSG.Sporadic.HNSchreier.Native
