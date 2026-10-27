module

public import Certificates.Data.CFSGNative.He.Fp
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.He.Native

open CFSG.Sporadic.Th.Native

structure VOrbit where
  keys : Array (Array Nat)
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def vecBFS (p d : Nat) (A B : Array (Array Nat)) (v₀ : Array Nat) (cap : Nat) :
    VOrbit := Id.run do
  let mut keys : Array (Array Nat) := #[v₀]
  let mut index : Std.HashMap (Array Nat) Nat := (∅ : Std.HashMap _ _).insert v₀ 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  for h in [0:cap] do
    if h < keys.size then
      let X := keys[h]!
      let Ya := mulVec p d A X
      match index[Ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert Ya keys.size
        alpha := alpha.push (UInt32.ofNat keys.size)
        keys := keys.push Ya
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let Yb := mulVec p d B X
      match index[Yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert Yb keys.size
        beta := beta.push (UInt32.ofNat keys.size)
        keys := keys.push Yb
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  return ⟨keys, alpha, beta, par, lab⟩

@[expose] def indexOf (keys : Array (Array Nat)) : Std.HashMap (Array Nat) Nat :=
  (List.range keys.size).foldl (fun m i => m.insert keys[i]! i) ∅

@[inline, expose] def vecCheckAt (p d : Nat) (A B : Array (Array Nat)) (O : VOrbit)
    (pos : Array Nat → Nat) (k : Nat) : Bool :=
  let N := O.keys.size
  let X := O.keys[k]!
  let ka := ap O.alpha k
  let kb := ap O.beta k
  canonV p d X && pos X == k && ka < N && mulVec p d A X == O.keys[ka]! &&
    kb < N && mulVec p d B X == O.keys[kb]! &&
    (k == 0 || (ap O.par k < k &&
      ((ap O.lab k == 1 && ap O.alpha (ap O.par k) == k) ||
        (ap O.lab k == 2 && ap O.beta (ap O.par k) == k))))

@[expose] def vecOrbitOK (p d : Nat) (A B : Array (Array Nat)) (v₀ : Array Nat) (O : VOrbit)
    (chunks : Nat) : Bool :=
  let index := indexOf O.keys
  0 < O.keys.size && O.keys.size < 2 ^ 32 && O.keys[0]! == v₀ &&
    parAll O.keys.size chunks (vecCheckAt p d A B O (fun X => index.getD X O.keys.size))

end CFSG.Sporadic.He.Native
