module

public import Certificates.Data.CFSGNative.J1.Vec

public section

namespace CFSG.Sporadic.J1.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[inline, expose] def inTree (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

structure PrimData where
  lab : Array Nat
  reps : Array Nat
  subs : Array Tree
  imgs : Array (Array Nat)
  ders : Array (List (Nat × Nat))
deriving Inhabited

@[expose] def suborbits (n : Nat) (letters : Array Table) (lv : Array Nat) :
    Array Nat × Array Nat × Array Tree := Id.run do
  let mut lab : Array Nat := Array.replicate n n
  let mut reps : Array Nat := #[]
  let mut subs : Array Tree := #[]
  for p in [0:n] do
    if lab[p]! == n then
      let T := treeBFS n p letters lv
      let l := reps.size
      for q in T.pts do
        lab := lab.set! q.toNat l
      reps := reps.push p
      subs := subs.push T
  return (lab, reps, subs)

@[inline, expose] def derStep (n k : Nat) (lab : Array Nat) (imgs : Array (Array Nat))
    (D : Array Bool) (s : Nat × Nat) : Array Bool :=
  if s.1 < k && s.2 < n && D[s.1]! && D[lab[s.2]!]! then
    D.set! lab[(imgs[s.1]!)[s.2]!]! true
  else D

@[expose] def derRun (n k l0 i : Nat) (lab : Array Nat) (imgs : Array (Array Nat))
    (steps : List (Nat × Nat)) : Array Bool :=
  steps.foldl (derStep n k lab imgs) (((Array.replicate k false).set! l0 true).set! i true)

@[expose] def derOK (n k l0 i : Nat) (lab : Array Nat) (imgs : Array (Array Nat))
    (steps : List (Nat × Nat)) : Bool :=
  let D := derRun n k l0 i lab imgs steps
  D.size == k && allIn 0 k fun l => D[l]!

@[expose] def derSearch (n k l0 i : Nat) (lab : Array Nat) (imgs : Array (Array Nat)) :
    List (Nat × Nat) := Id.run do
  let mut D : Array Bool := ((Array.replicate k false).set! l0 true).set! i true
  let mut steps : Array (Nat × Nat) := #[]
  for _ in [0:k + 1] do
    for j in [0:k] do
      if D[j]! then
        let im := imgs[j]!
        for w in [0:n] do
          if D[lab[w]!]! then
            let l := lab[im[w]!]!
            if !D[l]! then
              D := D.set! l true
              steps := steps.push (j, w)
  return steps.toList

@[expose] def treeImg (n : Nat) (T0 : Tree) (letters : Array Table) (r : Nat) : Array Nat :=
  walk T0 letters (ap T0.pos r) (Array.range n)

@[expose] def primData (n : Nat) (letters : Array Table) (lv : Array Nat) (T0 : Tree) :
    PrimData :=
  let (lab, reps, subs) := suborbits n letters lv
  let k := reps.size
  let imgs := reps.map fun r => treeImg n T0 letters r
  let l0 := lab[0]!
  let ders := (Array.range k).map fun i => if i == l0 then [] else derSearch n k l0 i lab imgs
  ⟨lab, reps, subs, imgs, ders⟩

@[expose] def primOK (n : Nat) (letters : Array Table) (lv : Array Nat) (T0 : Tree)
    (D : PrimData) : Bool :=
  let k := D.reps.size
  D.lab.size == n && D.subs.size == k && D.imgs.size == k && D.ders.size == k && 0 < n &&
    allIn 0 k (fun l => D.reps[l]! < n && D.lab[D.reps[l]!]! == l && inTree T0 D.reps[l]! &&
      CFSG.Perm.Native.treeOK n D.reps[l]! D.subs[l]! letters lv &&
      D.imgs[l]! == treeImg n T0 letters D.reps[l]! &&
      (l == D.lab[0]! || derOK n k D.lab[0]! l D.lab D.imgs D.ders[l]!)) &&
    allIn 0 n (fun p => D.lab[p]! < k && inTree D.subs[D.lab[p]!]! p)

end CFSG.Sporadic.J1.Native
