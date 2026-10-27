module

public import Certificates.Data.CFSGNative.H13.LocDblDc
public import Certificates.Data.CFSGNative.Co2Rank.Dfs
public import Std.Data.HashMap

public section

namespace CFSG.Quasithin.H13.LocDbl.DcRank

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Sporadic.Co2Rank

@[expose] def compT (t u : Array Nat) : Array Nat := u.map fun q => img t q

@[expose] def idT (n : Nat) : Array Nat := Array.range n

@[expose] def elemTabs (D : DcData) : Array (Array Nat) :=
  let PA := (Array.range D.n).map (ptsArr D.RT D.rpar D.rlab D.NR)
  (Array.range D.NR).map fun k => PA.map fun A => A.getD k 0

@[expose] def isInvT (n : Nat) (t : Array Nat) : Bool :=
  (compT t t == idT n) && (t != idT n)

@[expose] def invIdx (D : DcData) (T : Array (Array Nat)) : List Nat :=
  (List.range D.NR).filter fun k => decide (0 < k) && isInvT D.n (T.getD k #[])

@[expose] def invUniv (D : DcData) (T : Array (Array Nat)) : Array (Array Nat) :=
  ((invIdx D T).map fun k => T.getD k #[]).toArray

@[expose] def posMapP (V : Array (Array Nat)) : Std.HashMap (Array Nat) Nat :=
  (List.range V.size).foldl (fun m k => m.insert V[k]! k) ∅

@[expose] def prP (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) (i j : Nat) : Nat :=
  pos.getD (compT V[i]! V[j]!) V.size

@[expose] def adjP (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) (i j : Nat) : Bool :=
  decide (i < V.size) && decide (j < V.size) && (compT V[i]! V[j]! == compT V[j]! V[i]!) &&
    decide (prP V pos i j < V.size) && (V[prP V pos i j]! == compT V[i]! V[j]!)

@[expose] def adjTab (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) : Array Bool :=
  Array.ofFn (n := V.size * V.size) fun ij => adjP V pos (ij.val / V.size) (ij.val % V.size)

@[expose] def prTab (V : Array (Array Nat)) (pos : Std.HashMap (Array Nat) Nat) : Array Nat :=
  Array.ofFn (n := V.size * V.size) fun ij => prP V pos (ij.val / V.size) (ij.val % V.size)

@[expose] def adjQ (N : Nat) (t : Array Bool) (i j : Nat) : Bool :=
  decide (i < N) && decide (j < N) && t.getD (i * N + j) false

@[expose] def prQ (N : Nat) (t : Array Nat) (i j : Nat) : Nat := t.getD (i * N + j) 0

@[expose] def rankCheck (D : DcData) (d : Nat) : Bool :=
  let T := elemTabs D
  let V := invUniv D T
  let N := V.size
  let pos := posMapP V
  let adjT := adjTab V pos
  let prT := prTab V pos
  (List.range N).all (fun k => pos.getD V[k]! N == k) &&
    dfs (adjQ N adjT) (prQ N prT) d [] (List.range N) 0

end CFSG.Quasithin.H13.LocDbl.DcRank
