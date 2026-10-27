module

public import Certificates.Data.CFSGNative.Th.Data
public import Certificates.Data.CFSGNative.Th.FormCheck

public section

namespace CFSG.Sporadic.Th.Native

@[expose] def bitN (b : Bool) : Nat := if b then 1 else 0

@[expose] def gramCodeN (fT : Array V4) (ki kj : Key) : Nat :=
  let f0 := frApply fT kj.u
  let f1 := frApply fT kj.v
  bitN (ki.u.dot f0) + 2 * bitN (ki.u.dot f1) + 4 * bitN (ki.v.dot f0) + 8 * bitN (ki.v.dot f1)

@[expose] def formT (_ : Unit) : Array V4 := frTable (transposeRows fcRows)

@[expose] def baseCode (i j : Nat) : Nat := gramCodeN (formT ()) (deltaKeys[i]!) (deltaKeys[j]!)

@[expose] def cRows (_ : Unit := ()) : Array V4 :=
  Array.ofFn (n := 248) fun k =>
    if k.val % 2 = 0 then (deltaKeys[k.val / 2]!).u else (deltaKeys[k.val / 2]!).v

@[expose] def invRows (X : Array V4) : Array V4 := Id.run do
  let mut m := X
  let mut r := idRows
  for c in [0:248] do
    let mut p := 248
    for i in [c:248] do
      if p == 248 && (m[i]!).testBit c then p := i
    if p < 248 then
      let mc := m[p]!
      let rc := r[p]!
      m := (m.set! p m[c]!).set! c mc
      r := (r.set! p r[c]!).set! c rc
      for i in [0:248] do
        if i != c && (m[i]!).testBit c then
          m := m.set! i ((m[i]!).xor mc)
          r := r.set! i ((r[i]!).xor rc)
  return r

end CFSG.Sporadic.Th.Native
