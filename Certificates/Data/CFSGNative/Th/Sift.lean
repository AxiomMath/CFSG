module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.Th.Native

@[inline, expose] def treeEdge (pl : Table) (s i j : Nat) : Bool :=
  0 < j && treePar (pl[j]!).toNat == i && treeLab (pl[j]!).toNat == s

@[inline, expose] def reqTwo (pl : Table) (P : Nat → Nat) (s i : Nat) : Bool :=
  let j := P i
  !treeEdge pl s i j && (j == i || (!treeEdge pl s j i && j < i))

@[inline, expose] def reqThree (pl : Table) (P : Nat → Nat) (s i : Nat) : Bool :=
  let j := P i
  let k := P j
  !treeEdge pl s i j && (j == i || ((!treeEdge pl s j k && j < i) || (!treeEdge pl s k i && k < i)))

structure Chain where
  pl0 : Table
  pos0 : Table
  inv0 : Nat → Table
  pts1 : Table
  pl1 : Table
  inv1 : Nat → Table

@[inline, expose] def strip (c : Chain) (q : Array Nat) : Option (Array Nat) :=
  let k0 := ap c.pos0 q[1]!
  if k0 == 0xFFFFFFFF then none else
  let q := applyTreeInv c.pl0 c.inv0 k0 q
  let k1 := findPt c.pts1 q[2]!
  if k1 < c.pts1.size then some (applyTreeInv c.pl1 c.inv1 k1 q) else none

@[inline, expose] def strip1 (c : Chain) (q : Array Nat) : Option (Array Nat) :=
  let k1 := findPt c.pts1 q[2]!
  if k1 < c.pts1.size then some (applyTreeInv c.pl1 c.inv1 k1 q) else none

@[expose] def tuple0 (_ : Unit := ()) : Array Nat := Array.ofFn (n := 124) fun i => i.val

@[inline, expose] def schreierTuple (pl : Table) (gens gensInv : Nat → Table) (s i : Nat) :
    Array Nat :=
  applyTreeInv pl gensInv (ap (gens s) i) (apT (gens s) (applyTree pl gens i tuple0))

@[inline, expose] def globalTest (pl : Table) (gens gensInv : Nat → Table) (c : Chain) (s i : Nat) :
    Bool :=
  match strip c (schreierTuple pl gens gensInv s i) with
  | some q => q == tuple0
  | none => false

@[inline, expose] def levelOneTest (pts0 : Table) (c : Chain) (gens : Nat → Table) (s k : Nat) :
    Bool :=
  let q := applyTreeInv c.pl0 c.inv0 (ap c.pos0 (ap (gens s) (ap pts0 k)))
    (apT (gens s) (applyTree c.pl0 gens k tuple0))
  match strip1 c q with
  | some q => q == tuple0
  | none => false

@[inline, expose] def levelTwoTest (c : Chain) (gens : Nat → Table) (s k : Nat) : Bool :=
  applyTreeInv c.pl1 c.inv1 (findPt c.pts1 (ap (gens s) (ap c.pts1 k)))
    (apT (gens s) (applyTree c.pl1 gens k tuple0)) == tuple0

end CFSG.Sporadic.Th.Native
