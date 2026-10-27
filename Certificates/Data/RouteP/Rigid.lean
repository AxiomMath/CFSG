module

public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def toTables (gens : Array (Array Nat)) : Array Table :=
  gens.map fun g => g.map UInt32.ofNat

@[expose] def tablesOK (n : Nat) (gens : Array (Array Nat)) : Bool :=
  decide (n < 2 ^ 32) && gens.all (fun g => g.size == n && g.all (· < n)) &&
    (toTables gens).all fun T => invOK n T (invT n T)

@[inline, expose] def inTree (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def orbitTrees (n : Nat) (letters : Array Table) : List Tree := Id.run do
  let lv := Array.range letters.size
  let mut seen : Array Bool := Array.replicate n false
  let mut out : Array Tree := #[]
  for r in [0:n] do
    if !seen[r]! then
      let T := treeBFS n r letters lv
      for p in T.pts do
        seen := seen.set! p.toNat true
      out := out.push T
  return out.toList

@[expose] def propagate (T : Tree) (letters : Array Table) (c : Nat) (k : Nat) : Nat :=
  if _h : 0 < k ∧ ap T.par k < k then
    ap letters[ap T.lab k]! (propagate T letters c (ap T.par k))
  else c
termination_by k

@[expose] def candOK (letters : Array Table) (T : Tree) (c : Nat) : Bool :=
  let m := T.pts.size
  let fT : Array Nat := Array.ofFn (n := m) fun k => propagate T letters c k.val
  allIn 0 m fun k =>
    allIn 0 letters.size fun l =>
      fT[ap T.pos (ap letters[l]! (ap T.pts k))]! == ap letters[l]! fT[k]!

@[expose] def candList (letters : Array Table) (T : Tree) : List Nat :=
  (T.pts.toList.map UInt32.toNat).filter (candOK letters T)

@[expose] def combined (letters : Array Table) : List Tree → List Nat → Nat → Nat
  | T :: Ts, c :: cs, v =>
    if inTree T v then propagate T letters c (ap T.pos v) else combined letters Ts cs v
  | _, _, v => v

@[expose] def allSections {α : Type} : List (List α) → (List α → Bool) → Bool
  | [], p => p []
  | cs :: rest, p => cs.all fun c => allSections rest fun l => p (c :: l)

@[expose] def preservesR (n : Nat) (R : Nat → Nat → Nat) (f : Array Nat) : Bool :=
  allIn 0 n fun a => let fa := f[a]!; allIn 0 n fun b => R fa f[b]! == R a b

@[expose] def rigidOKAt (n : Nat) (gens : Array (Array Nat)) (R : Nat → Nat → Nat)
    (trees : List Tree) : Bool :=
  let letters := toTables gens
  let lv := Array.range gens.size
  tablesOK n gens && trees.all (fun T => treeOK n (ap T.pts 0) T letters lv) &&
    allIn 0 n (fun v => trees.any fun T => inTree T v) &&
    (trees.map fun T => T.pts.size).sum == n && decide ((trees.map fun T => T.pts.size).Nodup) &&
    allSections (trees.map (candList letters)) fun cs =>
      cs == trees.map (fun T => ap T.pts 0) ||
        !preservesR n R (Array.ofFn (n := n) fun v => combined letters trees cs v.val)

@[expose] def rigidOK (n : Nat) (gens : Array (Array Nat)) (R : Nat → Nat → Nat) : Bool :=
  tablesOK n gens && rigidOKAt n gens R (orbitTrees n (toTables gens))

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native
