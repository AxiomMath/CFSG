module

public import Certificates.Data.CFSGNative.Fi23.Wide
public import Certificates.Data.CFSGNative.Perm.Chain
public import Certificates.Data.CFSGNative.HS.Cert
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.ON.Native

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

@[inline, expose] def canon154 (a : W) : Bool :=
  a.wf && a.p2 >>> 26 == 0 && a.m2 >>> 26 == 0 && a.p3 == 0 && a.m3 == 0

@[inline, expose] def mulVecT (Mt : Array W) (x : W) : W := combW 154 Mt x

structure VOrbit where
  keys : Array W
  alpha : Table
  beta : Table
deriving Inhabited

@[expose] def orbitBFS (cA cB : Array W) (v₀ : W) (cap : Nat) : VOrbit := Id.run do
  let mut keys : Array W := #[v₀]
  let mut index : Std.HashMap W Nat := (∅ : Std.HashMap W Nat).insert v₀ 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  for h in [0:cap] do
    if h < keys.size then
      let x := keys[h]!
      let ya := mulVecT cA x
      match index[ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert ya keys.size
        alpha := alpha.push (UInt32.ofNat keys.size)
        keys := keys.push ya
      let yb := mulVecT cB x
      match index[yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert yb keys.size
        beta := beta.push (UInt32.ofNat keys.size)
        keys := keys.push yb
    else break
  return ⟨keys, alpha, beta⟩

@[expose] def indexOf (keys : Array W) : Std.HashMap W Nat :=
  (List.range keys.size).foldl (fun m i => m.insert keys[i]! i) ∅

@[inline, expose] def orbitCheckAt (n : Nat) (cA cB : Array W) (O : VOrbit) (pos : W → Nat)
    (i : Nat) : Bool :=
  let x := O.keys[i]!
  canon154 x && pos x == i && ap O.alpha i < n && O.keys[ap O.alpha i]! == mulVecT cA x &&
    ap O.beta i < n && O.keys[ap O.beta i]! == mulVecT cB x

@[expose] def orbitOK (n : Nat) (cA cB : Array W) (O : VOrbit) (pos : W → Nat) (chunks : Nat) :
    Bool :=
  O.keys.size == n && O.alpha.size == n && O.beta.size == n &&
    parAll n chunks (orbitCheckAt n cA cB O pos)

@[expose] def negTable (O : VOrbit) (pos : W → Nat) : Table :=
  O.keys.map fun x => UInt32.ofNat (pos x.neg)

@[expose] def negOK (n : Nat) (O : VOrbit) (N : Table) : Bool :=
  allIn 0 n fun i => ap N i < n && O.keys[ap N i]! == O.keys[i]!.neg

@[expose] def gjStep (d : Nat) (A : Array V) (c : Nat) : Array V := Id.run do
  let mut piv := d
  for r in [c:d] do
    if piv == d && A[r]!.get c != 0 then piv := r
  if piv < d then
    let mut A := A
    let rowP := A[piv]!
    A := (A.set! piv A[c]!).set! c rowP
    if A[c]!.get c == 2 then A := A.set! c A[c]!.neg
    let rc := A[c]!
    for r in [0:d] do
      if r != c then
        let f := A[r]!.get c
        if f == 1 then A := A.set! r (A[r]!.sub rc)
        else if f == 2 then A := A.set! r (A[r]!.add rc)
    return A
  else return A

@[expose] def invV (d : Nat) (X : Array V) : Array V := Id.run do
  let mut A : Array V := Array.ofFn (n := d) fun i =>
    ⟨X[i.val]!.p ||| (1 <<< (d + i.val)), X[i.val]!.m⟩
  for c in [0:d] do
    A := gjStep d A c
  return A.map fun r => ⟨r.p >>> d, r.m >>> d⟩

@[expose] def invW (d : Nat) (X : Array W) : Array W := (invV d (toVM X)).map ofV

end CFSG.Sporadic.ON.Native
