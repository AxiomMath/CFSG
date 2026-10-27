module

public import Certificates.Data.CFSGNative.Ly.Certificate

public section

namespace CFSG.Sporadic.Ly.ThreeB

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.LevelChain.Native
  CFSG.Sporadic.Ly.Native

@[expose] def gWord : List Int :=
  [2, 1, -2, 2, -2, -2, 2, -2, 1, 2, 2, 1, -2, -2, 2, -2, 2, -2, 1, -2, 2, 2, 2, 2, 1, 1, -2, -2,
    1, 1, 1, -2, 1, -2, -2, -2, -2, -2, -2, -2, -2, -2, 1, -2, -2, 2, -2]

@[expose] def yTable (alpha beta : Table) : Table :=
  powT nPts 6 (wordT nPts (genTables alpha beta) gWord)

@[expose] def pt0 : Nat := 1

@[inline, expose] def triple (Y : Table) (p : Nat) : Array Nat := #[p, ap Y p, ap Y (ap Y p)]

@[expose] def strip1 (T : Array Tree) (L : Array Table) (img : Array Nat) : Array Nat :=
  walkInv T[0]! L (ap T[0]!.pos img[0]!) img

@[expose] def strip2 (T : Array Tree) (L : Array Table) (img : Array Nat) : Array Nat :=
  walkInv T[1]! L (ap T[1]!.pos (strip1 T L img)[1]!) (strip1 T L img)

@[expose] def countIn (lo hi : Nat) (f : Nat → Bool) : Nat :=
  Nat.fold (hi - lo) (fun k _ acc => if f (lo + k) then acc + 1 else acc) 0

@[expose] def countBlocks (n b : Nat) (f : Nat → Bool) : Nat :=
  ((List.range ((n + b - 1) / b)).map fun j =>
    Task.spawn fun _ => countIn (j * b) (min n ((j + 1) * b)) f).foldl (fun a t => a + t.get) 0

@[expose] def scanCount (trees : Array Tree) (L : Array Table) (Y : Table) (Q : Array Nat) : Nat :=
  countBlocks nPts 65536 fun p => sift trees L chainQb Q 0 (triple Y p)

@[expose] def threeBCheck (alpha beta : Table) : Bool :=
  let L := chainLetters alpha beta
  let T := levelTrees nPts L chainStarts chainBase
  let Y := yTable alpha beta
  let img₀ := triple Y pt0
  let Q := strip2 T L img₀
  let T2 := treeBFS nPts Q[2]! L (levelLv chainStarts 2)
  order3OK nPts Y && ap Y pt0 != pt0 &&
    ap T[0]!.pos img₀[0]! < T[0]!.pts.size &&
    ap T[1]!.pos (strip1 T L img₀)[1]! < T[1]!.pts.size &&
    Q.size == 3 && Q[0]! == 0 && Q[1]! == 3 &&
    treeOK nPts Q[2]! T2 L (levelLv chainStarts 2) && T2.pts.size == 2880 &&
    decide (scanCount #[T[0]!, T[1]!, T2] L Y Q ≤ 174960)

@[expose] def threeBCertificate (_ : Unit) : Bool :=
  let O := orbitData ()
  threeBCheck O.alpha O.beta

end CFSG.Sporadic.Ly.ThreeB
