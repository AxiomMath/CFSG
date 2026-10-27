module

public import Certificates.Data.CFSGNative.J4.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.J4.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[inline, expose] def imgTuple (keys slots : ByteArray) (t : Array V2) (q : Array Nat) :
    Array Nat :=
  q.map fun p => findIdx keys slots (frApply t (rdV2 keys p)) - 1

@[expose] def tupleGroup (keys slots : ByteArray) (ts : Array (Array V2)) (q0 : Array Nat)
    (cap : Nat) : Array (Array Nat) × Array Nat × Array Nat × Std.HashMap (Array Nat) Nat :=
  Id.run do
  let mut tup : Array (Array Nat) := #[q0]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut m : Std.HashMap (Array Nat) Nat := (Std.HashMap.emptyWithCapacity cap).insert q0 0
  for e in [0:cap] do
    if e < tup.size then
      for g in [0:ts.size] do
        let img := imgTuple keys slots ts[g]! tup[e]!
        if !m.contains img && tup.size < cap then
          m := m.insert img tup.size
          tup := tup.push img
          par := par.push e
          lab := lab.push g
    else break
  return (tup, par, lab, m)

@[inline, expose] def tupleAt (keys : ByteArray) (n : Nat) (ts : Array (Array V2)) (m : Nat)
    (tup : Array (Array Nat)) (par lab : Array Nat) (k : Nat) : Bool :=
  k == 0 || (par[k]! < k && lab[k]! < ts.size && tup[k]!.size == m &&
    (List.range m).all fun t => (tup[k]!)[t]! < n &&
      (rdV2 keys (tup[k]!)[t]!).beq (frApply ts[lab[k]!]! (rdV2 keys (tup[par[k]!]!)[t]!)))

@[expose] def tupleGroupOK (keys : ByteArray) (n : Nat) (ts : Array (Array V2)) (q0 : Array Nat)
    (tup : Array (Array Nat)) (par lab : Array Nat) : Bool :=
  tup.size == par.size && tup.size == lab.size && 0 < tup.size && tup[0]! == q0 &&
    (List.range tup.size).all (tupleAt keys n ts q0.size tup par lab)

end CFSG.Sporadic.J4.Native
