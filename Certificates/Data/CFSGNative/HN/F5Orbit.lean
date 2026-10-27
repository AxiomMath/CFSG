module

public import Certificates.Data.CFSGNative.HN.F5Packed
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.F5.Native

open CFSG.Sporadic.Th.Native

structure VOrbit where
  keys : Array ByteArray
  alpha : Table
  beta : Table
  par : Table
  lab : Table
  index : Std.HashMap ByteArray Nat

instance : Inhabited VOrbit := ⟨⟨#[], #[], #[], #[], #[], ∅⟩⟩

@[expose] def f5OrbitBFS (d : Nat) (TA TB : Array W17) (v₀ : ByteArray) (cap : Nat) : VOrbit :=
    Id.run do
  let mut keys : Array ByteArray := Array.mkEmpty cap
  keys := keys.push v₀
  let mut index : Std.HashMap ByteArray Nat := (Std.HashMap.emptyWithCapacity cap).insert v₀ 0
  let mut alpha : Table := Array.mkEmpty cap
  let mut beta : Table := Array.mkEmpty cap
  let mut par : Table := (Array.mkEmpty cap).push 0
  let mut lab : Table := (Array.mkEmpty cap).push 0
  for h in [0:cap] do
    if h < keys.size then
      let X := keys[h]!
      let Ya := mulW d d TA X
      match index[Ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert Ya keys.size
        alpha := alpha.push (UInt32.ofNat keys.size)
        keys := keys.push Ya
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let Yb := mulW d d TB X
      match index[Yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert Yb keys.size
        beta := beta.push (UInt32.ofNat keys.size)
        keys := keys.push Yb
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  return ⟨keys, alpha, beta, par, lab, index⟩

@[inline, expose] def f5OrbitCheckAt (d : Nat) (TA TB : Array W17) (O : VOrbit) (k : Nat) : Bool :=
  let N := O.keys.size
  let X := O.keys[k]!
  let ka := ap O.alpha k
  let kb := ap O.beta k
  canonB d X && O.index.getD X N == k && ka < N && mulW d d TA X == O.keys[ka]! &&
    kb < N && mulW d d TB X == O.keys[kb]! &&
    (k == 0 || (ap O.par k < k &&
      ((ap O.lab k == 1 && ap O.alpha (ap O.par k) == k) ||
        (ap O.lab k == 2 && ap O.beta (ap O.par k) == k))))

@[expose] def f5OrbitOK (d : Nat) (TA TB : Array W17) (v₀ : ByteArray) (O : VOrbit)
    (chunks : Nat) : Bool :=
  0 < O.keys.size && O.keys.size < 2 ^ 32 && O.keys[0]! == v₀ &&
    parAll O.keys.size chunks (f5OrbitCheckAt d TA TB O)

end CFSG.Sporadic.F5.Native
