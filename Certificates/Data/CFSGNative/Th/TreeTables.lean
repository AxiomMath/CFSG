module

public import Certificates.Data.CFSGNative.Th.Certificate

public section

namespace CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def treePath (pl : Table) (k : Nat) : List Nat :=
  if _h : 0 < k ∧ treePar (pl[k]!).toNat < k then
    treePath pl (treePar (pl[k]!).toNat) ++ [treeLab (pl[k]!).toNat]
  else []
termination_by k

@[expose] def pathEntry (ts : List Table) (y : UInt32) : UInt32 :=
  ts.foldl (fun y T => T[y.toNat]!) y

@[expose] def treeRows (ts : List Table) (lo hi : Nat) : Table :=
  Array.ofFn (n := hi - lo) fun i => pathEntry ts (UInt32.ofNat (lo + i.val))

@[expose] def chunkSize (n : Nat) : Nat := n / 32 + 1

@[expose] def treeTableTasks (n : Nat) (pl : Table) (gens : Nat → Table) (k : Nat) : Table :=
  let ts := (treePath pl k).map gens
  let sz := chunkSize n
  let parts : Array (Task Table) := Array.ofFn (n := 32) fun j =>
    Task.spawn fun _ => treeRows ts (j.val * sz) (min ((j.val + 1) * sz) n)
  let rows : Array Table := parts.map Task.get
  Array.ofFn (n := n) fun x => (rows[x.val / sz]!)[x.val % sz]!

@[expose] def splitRangeTh (lo hi : Nat) : Nat → List (Nat × Nat)
  | 0 => [(lo, hi)]
  | d + 1 => splitRangeTh lo ((lo + hi) / 2) d ++ splitRangeTh ((lo + hi) / 2) hi d

@[expose] def treeOKTasks (n m root : Nat) (pts pl : Table) (lk : Nat → Nat) (g1 g2 : Table) :
    Bool :=
  0 < m && ap pts 0 == root &&
    ((splitRangeTh 0 m 5).map fun r =>
      Task.spawn fun _ => allIn r.1 r.2 (treeCheckAt n m pts pl lk g1 g2)).all Task.get


@[specialize, expose] def pushRange (f : Nat → UInt32) (hi i : Nat) (acc : Table) : Table :=
  if i < hi then pushRange f hi (i + 1) (acc.push (f i)) else acc
termination_by hi - i

@[specialize, expose] def parTable (n : Nat) (f : Nat → UInt32) : Table :=
  ((Array.ofFn (n := n >>> 22 + 1) fun j =>
    Task.spawn fun _ => pushRange f (min n ((j.val + 1) <<< 22)) (j.val <<< 22)
      (Array.mkEmpty 4194304)).map Task.get).flatten

@[expose] def compTP (n : Nat) (P Q : Table) : Table := parTable n fun i => P[(Q[i]!).toNat]!

@[expose] def tblOfBytesP (n : Nat) (b : ByteArray) : Table :=
  parTable n fun i => UInt32.ofNat (readU32 b i)

@[expose] def powIter (P : Table) : Nat → UInt32 → UInt32
  | 0, y => y
  | e + 1, y => P[(powIter P e y).toNat]!

@[expose] def powTP (n e : Nat) (P : Table) : Table :=
  parTable n fun i => powIter P e (UInt32.ofNat i)

@[expose] def wordIter (ts : List Table) (y : UInt32) : UInt32 :=
  ts.foldr (fun T y => T[y.toNat]!) y

@[expose] def wordTP (n : Nat) (ts : List Table) : Table :=
  let rs := ts.reverse
  parTable n fun i => pathEntry rs (UInt32.ofNat i)

@[specialize, expose] def allInP (n : Nat) (p : Nat → Bool) : Bool :=
  ((splitRangeTh 0 n 5).map fun r => Task.spawn fun _ => allIn r.1 r.2 p).all Task.get

@[expose] def invOKP (n : Nat) (P R : Table) : Bool := allInP n fun i => ap R (ap P i) == i

@[expose] def treeOKPos (n m root : Nat) (pts pl pos : Table) (g1 g2 : Table) : Bool :=
  0 < m && ap pts 0 == root &&
    ((splitRangeTh 0 m 5).map fun r =>
      Task.spawn fun _ => allIn r.1 r.2 (treeCheckAt n m pts pl (ap pos) g1 g2)).all Task.get

@[expose] def treeTableP (n : Nat) (pl : Table) (gens : Nat → Table) (k : Nat) : Table :=
  let ts := (treePath pl k).map gens
  parTable n fun i => pathEntry ts (UInt32.ofNat i)

end CFSG.Sporadic.Th.Native
