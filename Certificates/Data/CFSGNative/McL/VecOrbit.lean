module

public import Certificates.Data.CFSGNative.F3.Sep
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.VecOrbit.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native

structure VOrbit where
  pts : Array V
  alpha : Table
  beta : Table
  par : Table
  lab : Table
deriving Inhabited

@[inline, expose] def vkey (v : V) : Nat × Nat := (v.p, v.m)

@[expose] def vecBFS (d : Nat) (AT BT : Array V) (v0 : V) (cap : Nat) : VOrbit := Id.run do
  let mut pts : Array V := #[v0]
  let mut index : Std.HashMap (Nat × Nat) Nat := (∅ : Std.HashMap _ _).insert (vkey v0) 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  for h in [0:cap] do
    if h < pts.size then
      let X := pts[h]!
      let Ya := comb d AT X
      match index[vkey Ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert (vkey Ya) pts.size
        alpha := alpha.push (UInt32.ofNat pts.size)
        pts := pts.push Ya
        par := par.push (UInt32.ofNat h)
        lab := lab.push 1
      let Yb := comb d BT X
      match index[vkey Yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert (vkey Yb) pts.size
        beta := beta.push (UInt32.ofNat pts.size)
        pts := pts.push Yb
        par := par.push (UInt32.ofNat h)
        lab := lab.push 2
    else break
  return ⟨pts, alpha, beta, par, lab⟩

@[expose] def vindexOf (pts : Array V) : Std.HashMap (Nat × Nat) Nat :=
  (List.range pts.size).foldl (fun m i => m.insert (vkey pts[i]!) i) ∅

@[inline, expose] def vecCheckAt (d : Nat) (AT BT : Array V) (O : VOrbit) (pos : V → Nat)
    (k : Nat) : Bool :=
  let N := O.pts.size
  let X := O.pts[k]!
  let ka := ap O.alpha k
  let kb := ap O.beta k
  X.canon d && pos X == k && ka < N && (comb d AT X).beq O.pts[ka]! &&
    kb < N && (comb d BT X).beq O.pts[kb]! &&
    (k == 0 || (ap O.par k < k &&
      ((ap O.lab k == 1 && ap O.alpha (ap O.par k) == k) ||
        (ap O.lab k == 2 && ap O.beta (ap O.par k) == k))))

@[expose] def vecOrbitOK (d : Nat) (AT BT : Array V) (O : VOrbit) (chunks : Nat) : Bool :=
  let index := vindexOf O.pts
  0 < O.pts.size && O.pts.size < 2 ^ 32 &&
    parAll O.pts.size chunks
      (vecCheckAt d AT BT O (fun X => index.getD (vkey X) O.pts.size))

@[expose] def basisOK (d : Nat) (S Tinv : Array V) : Bool :=
  S.size == d && wfM S && wfM Tinv && Tinv.size == d && eqM d (mul d Tinv S) (idM d)

end CFSG.Sporadic.VecOrbit.Native
