module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Perm.Native

open CFSG.Sporadic.Th.Native

structure Tree where
  pts : Table
  pos : Table
  par : Table
  lab : Table
deriving Inhabited

@[inline, expose] def invL (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

@[expose] def treeBFS (n root : Nat) (letters : Array Table) (lv : Array Nat) : Tree := Id.run do
  let mut pos : Table := Array.replicate n none32
  let mut pts : Table := #[UInt32.ofNat root]
  let mut par : Table := #[0]
  let mut lab : Table := #[0]
  pos := pos.set! root 0
  for h in [0:n] do
    if h < pts.size then
      let p := ap pts h
      for l in lv do
        let q := ap letters[l]! p
        if pos[q]! == none32 then
          pos := pos.set! q (UInt32.ofNat pts.size)
          pts := pts.push (UInt32.ofNat q)
          par := par.push (UInt32.ofNat h)
          lab := lab.push (UInt32.ofNat l)
    else break
  return ⟨pts, pos, par, lab⟩

@[inline, expose] def treeAt (n : Nat) (T : Tree) (letters : Array Table) (lv : Array Nat)
    (k : Nat) : Bool :=
  let m := T.pts.size
  let p := ap T.pts k
  p < n && ap T.pos p == k &&
    lv.all (fun l => let q := ap letters[l]! p; ap T.pos q < m && ap T.pts (ap T.pos q) == q) &&
    (k == 0 || (ap T.par k < k && lv.contains (ap T.lab k) &&
      ap letters[ap T.lab k]! (ap T.pts (ap T.par k)) == p))

@[expose] def treeOK (n root : Nat) (T : Tree) (letters : Array Table) (lv : Array Nat) : Bool :=
  0 < T.pts.size && ap T.pts 0 == root && allIn 0 T.pts.size (treeAt n T letters lv)

@[expose] def walk (T : Tree) (letters : Array Table) (k : Nat) (q : Array Nat) : Array Nat :=
  if _h : 0 < k ∧ ap T.par k < k then
    apT letters[ap T.lab k]! (walk T letters (ap T.par k) q)
  else q
termination_by k

@[expose] def walkInv (T : Tree) (letters : Array Table) (k : Nat) (q : Array Nat) : Array Nat :=
  if _h : 0 < k ∧ ap T.par k < k then
    walkInv T letters (ap T.par k) (apT letters[invL (ap T.lab k)]! q)
  else q
termination_by k

@[inline, expose] def tupleEq (a b : Array Nat) : Bool :=
  a.size == b.size && allIn 0 b.size fun t => a[t]! == b[t]!

@[expose] def sift (trees : Array Tree) (letters : Array Table) (qb Q : Array Nat) (l : Nat)
    (img : Array Nat) : Bool :=
  if _h : l < trees.size then
    let T := trees[l]
    let k := ap T.pos img[qb[l]!]!
    k < T.pts.size && sift trees letters qb Q (l + 1) (walkInv T letters k img)
  else tupleEq img Q
termination_by trees.size - l

@[inline, expose] def schreierAt (trees : Array Tree) (letters : Array Table) (qb Q : Array Nat)
    (i l k : Nat) : Bool :=
  let T := trees[i]!
  let ky := ap T.pos (ap letters[l]! (ap T.pts k))
  ky < T.pts.size &&
    sift trees letters qb Q (i + 1) (walkInv T letters ky (apT letters[l]! (walk T letters k Q)))

@[expose] def levelLetters (letters : Array Table) (base : Array Nat) : Nat → Array Nat
  | 0 => Array.range letters.size
  | i + 1 => (levelLetters letters base i).filter fun l => ap letters[l]! base[i]! == base[i]!

@[expose] def chainTrees (n : Nat) (letters : Array Table) (base : Array Nat) : Array Tree :=
  Array.ofFn (n := base.size) fun i =>
    treeBFS n base[i.val]! letters (levelLetters letters base i.val)

@[expose] def chainOK (n : Nat) (letters : Array Table) (base Q qb : Array Nat)
    (trees : Array Tree) (chunks : Nat) : Bool :=
  let m := base.size
  letters.size % 2 == 0 &&
    allIn 0 (letters.size / 2) (fun j => invOK n letters[2 * j]! letters[2 * j + 1]!) &&
    trees.size == m && qb.size == m && allIn 0 Q.size (fun t => Q[t]! < n) &&
    allIn 0 m (fun i => qb[i]! < Q.size && Q[qb[i]!]! == base[i]!) &&
    allIn 0 m (fun i => treeOK n base[i]! trees[i]! letters (levelLetters letters base i)) &&
    allIn 0 m (fun i => (levelLetters letters base i).all fun l =>
      parAll trees[i]!.pts.size chunks (schreierAt trees letters qb Q i l)) &&
    (levelLetters letters base m).all fun l => tupleEq (apT letters[l]! Q) Q

@[expose] def buildLetters (n : Nat) (gens : Int → Table) (words : Array (List Int)) :
    Array Table :=
  Array.ofFn (n := 2 * words.size) fun i =>
    let t := wordT n gens words[i.val / 2]!
    if i.val % 2 = 0 then t else invT n t

@[expose] def orbitSizes (trees : Array Tree) : List Nat := trees.toList.map fun T => T.pts.size

end CFSG.Perm.Native
