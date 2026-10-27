module

public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.F3.Native

@[expose] def zeroM (d : Nat) : Array V := Array.replicate d V.zero

@[expose] def addM (d : Nat) (X Y : Array V) : Array V :=
  Array.ofFn (n := d) fun i => X[i.val]!.add Y[i.val]!

@[expose] def negM (X : Array V) : Array V := X.map V.neg

@[expose] def prodM (d : Nat) (mats : Array (Array V)) (word : List Nat) : Array V :=
  word.foldl (fun M x => mul d M mats[x]!) (idM d)

@[expose] def combM (d : Nat) (mats : Array (Array V)) (terms : List (Nat × List Nat)) :
    Array V :=
  terms.foldl (fun acc t => let M := prodM d mats t.2
    addM d acc (if t.1 == 2 then negM M else M)) (zeroM d)

@[inline, expose] def mulVecM (d : Nat) (M : Array V) (v : V) : V := comb d (transpose d M) v

@[expose] def outerRow (v : V) (k i : Nat) : V :=
  if v.get i = 1 then ⟨1 <<< k, 0⟩ else if v.get i = 2 then ⟨0, 1 <<< k⟩ else V.zero

@[expose] def projM (d : Nat) (v : V) (k : Nat) : Array V :=
  Array.ofFn (n := d) fun i => (⟨1 <<< i.val, 0⟩ : V).sub (outerRow v k i.val)

@[expose] def spinVecs (d : Nat) (mats : Array (Array V)) (v : V) (tree : List (Nat × Nat)) :
    Array V :=
  tree.foldl (fun S t => S.push (mulVecM d mats[t.2]! S[t.1]!)) #[v]

@[inline, expose] def V.isZero (a : V) : Bool := a.p == 0 && a.m == 0

@[inline, expose] def V.canon (d : Nat) (a : V) : Bool := a.wf && a.p >>> d == 0 && a.m >>> d == 0

@[expose] def sepOK (d : Nat) (mats : Array (Array V)) (terms : List (Nat × List Nat)) (v : V)
    (k : Nat) (P Tinv : Array V) (tree : List (Nat × Nat)) : Bool :=
  let w := combM d mats terms
  let S := spinVecs d mats v tree
  k < d && v.canon d && v.get k == 1 && mats.all wfM && wfM P && wfM Tinv &&
    P.size == d && Tinv.size == d &&
    terms.all (fun t => t.2.all (· < mats.size)) &&
    (mulVecM d w v).isZero && eqM d (mul d P w) (projM d v k) &&
    tree.all (fun t => t.2 < mats.size) &&
    (List.range tree.length).all (fun i => tree[i]!.1 ≤ i) &&
    S.size == d && eqM d (mul d Tinv S) (idM d)

end CFSG.F3.Native
