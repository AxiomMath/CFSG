module

public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.F3.Native

open CFSG.Sporadic.Th.Native

@[inline, expose] def conjM (d : Nat) (g gi X : Array V) : Array V := mul d (mul d g X) gi

@[expose] def canonM (d : Nat) (X : Array V) : Bool :=
  X.size == d && X.all fun v => v.wf && v.p >>> d == 0 && v.m >>> d == 0

@[inline, expose] def keyOf (X : Array V) : Array (Nat × Nat) := X.map fun v => (v.p, v.m)

structure COrbit where
  keys : Array (Array V)
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[expose] def conjBFS (d : Nat) (A Ai B Bi : Array V) (cap : Nat) : COrbit := Id.run do
  let mut keys : Array (Array V) := #[A]
  let mut index : Std.HashMap (Array (Nat × Nat)) Nat := (∅ : Std.HashMap _ _).insert (keyOf A) 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  for h in [0:cap] do
    if h < keys.size then
      let X := keys[h]!
      let Ya := conjM d A Ai X
      match index[keyOf Ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert (keyOf Ya) keys.size
        alpha := alpha.push (UInt32.ofNat keys.size)
        keys := keys.push Ya
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let Yb := conjM d B Bi X
      match index[keyOf Yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert (keyOf Yb) keys.size
        beta := beta.push (UInt32.ofNat keys.size)
        keys := keys.push Yb
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  return ⟨keys, alpha, beta, par, lab⟩

@[expose] def indexOf (keys : Array (Array V)) : Std.HashMap (Array (Nat × Nat)) Nat :=
  (List.range keys.size).foldl (fun m i => m.insert (keyOf keys[i]!) i) ∅

@[inline, expose] def conjCheckAt (d : Nat) (A Ai B Bi : Array V) (O : COrbit)
    (pos : Array V → Nat) (k : Nat) : Bool :=
  let N := O.keys.size
  let X := O.keys[k]!
  let ka := ap O.alpha k
  let kb := ap O.beta k
  canonM d X && pos X == k && ka < N && eqM d (conjM d A Ai X) O.keys[ka]! &&
    kb < N && eqM d (conjM d B Bi X) O.keys[kb]! &&
    (k == 0 || (ap O.par k < k &&
      ((ap O.lab k == 1 && ap O.alpha (ap O.par k) == k) ||
        (ap O.lab k == 2 && ap O.beta (ap O.par k) == k))))

@[expose] def conjOrbitOK (d : Nat) (A Ai B Bi : Array V) (O : COrbit) (chunks : Nat) : Bool :=
  let index := indexOf O.keys
  0 < O.keys.size && O.keys.size < 2 ^ 32 && eqM d O.keys[0]! A &&
    parAll O.keys.size chunks
      (conjCheckAt d A Ai B Bi O (fun X => index.getD (keyOf X) O.keys.size))

end CFSG.F3.Native
