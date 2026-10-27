module

public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.Sporadic.LevelChain.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

@[expose] def levelLv (starts : Array Nat) (i : Nat) : Array Nat :=
  Array.ofFn (n := 2 * (starts[i + 1]! - starts[i]!)) fun t => 2 * starts[i]! + t.val

@[inline, expose] def edgeTriv (T : Tree) (letters : Array Table) (s : Nat) (invo : Bool)
    (k : Nat) : Bool :=
  let ky := ap T.pos (ap letters[s]! (ap T.pts k))
  (0 < ky && ky < T.pts.size && ap T.par ky == k && ap T.lab ky == s) ||
    (0 < k && ap T.par k == ky && (ap T.lab k == s + 1 || (invo && ap T.lab k == s)))

@[expose] def iterAp (L : Table) : Nat → Nat → Nat
  | 0, x => x
  | i + 1, x => ap L (iterAp L i x)

@[expose] def cycleSkip (T : Tree) (letters : Array Table) (s d x : Nat) : Bool :=
  2 ≤ d && allIn 1 d fun i =>
    let y := iterAp letters[s]! i x
    y != x && (x < y || edgeTriv T letters s (d == 2) (ap T.pos y))

@[inline, expose] def levelTestAt (trees : Array Tree) (letters : Array Table) (qb Q : Array Nat)
    (i s d k : Nat) : Bool :=
  let T := trees[i]!
  edgeTriv T letters s (d == 2) k || cycleSkip T letters s d (ap T.pts k) ||
    schreierAt trees letters qb Q i s k

@[expose] def powFixes (L : Table) (e : Nat) (Q : Array Nat) : Bool :=
  tupleEq (Nat.repeat (apT L) e Q) Q

@[expose] def levelTrees (n : Nat) (letters : Array Table) (starts base : Array Nat) :
    Array Tree :=
  Array.ofFn (n := base.size) fun i => treeBFS n base[i.val]! letters (levelLv starts i.val)

@[expose] def levelChainOK (n : Nat) (letters : Array Table) (starts ords base Q qb : Array Nat)
    (trees : Array Tree) (chunks : Nat) : Bool :=
  let m := base.size
  letters.size == 2 * starts[m]! &&
    allIn 0 (letters.size / 2) (fun j => invOK n letters[2 * j]! letters[2 * j + 1]!) &&
    starts.size == m + 1 && allIn 0 m (fun i => starts[i]! ≤ starts[i + 1]!) &&
    trees.size == m && qb.size == m && allIn 0 Q.size (fun t => Q[t]! < n) &&
    allIn 0 m (fun i => qb[i]! < Q.size && Q[qb[i]!]! == base[i]!) &&
    allIn 0 m (fun i => treeOK n base[i]! trees[i]! letters (levelLv starts i)) &&
    allIn 1 m (fun i => allIn starts[i]! starts[i + 1]! fun j =>
      ap letters[2 * j]! base[i - 1]! == base[i - 1]!) &&
    ords.size == starts[m]! &&
    allIn 0 starts[m]! (fun j => 0 < ords[j]! && powFixes letters[2 * j]! ords[j]! Q) &&
    allIn 0 m (fun i => allIn starts[i]! starts[i + 1]! fun j =>
      parAll trees[i]!.pts.size chunks (levelTestAt trees letters qb Q i (2 * j) ords[j]!))

@[expose] def nestOK (words : Array (List Int)) (starts : Array Nat) : Bool :=
  words[0]! == [1] && words[1]! == [2] && 2 ≤ starts.size && starts[0]! == 0 &&
    starts[1]! == 2 && words.size == starts[starts.size - 1]! &&
    allIn 1 (starts.size - 1) fun i => allIn starts[i]! starts[i + 1]! fun j =>
      words[j]!.all fun z => decide (starts[i - 1]! + 3 ≤ z.natAbs) &&
        decide (z.natAbs < starts[i]! + 3)

end CFSG.Sporadic.LevelChain.Native
