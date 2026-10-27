module

public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.Sporadic.Schreier.Native

open CFSG.Sporadic.Th.Native

@[inline, expose] def apW (w : List Table) (i : Nat) : Nat := w.foldr (fun t j => ap t j) i

@[expose] def apPowW (w : List Table) : Nat → Nat → Nat
  | 0, i => i
  | e + 1, i => apW w (apPowW w e i)

@[expose] def powFixW (n : Nat) (w : List Table) (e : Nat) : Bool :=
  allIn 0 n fun i => apPowW w e i == i

@[expose] def divParts (m : Nat) : List Nat :=
  ((List.range (m + 1)).filter fun d => 1 < d && m % d == 0).map (m / ·)

@[expose] def ordW (n : Nat) (w : List Table) (m : Nat) : Bool :=
  powFixW n w m && (divParts m).all fun e => !powFixW n w e

@[expose] def ordTest (n m : Nat) (T : Table) : Bool := ordW n [T] m

@[expose] def commWord (x y : Table) (mx my : Nat) : List Table :=
  x :: y :: (List.replicate (mx - 1) x ++ List.replicate (my - 1) y)

@[expose] def pairTest (n r s mx my : Nat) (x y : Table) : Bool :=
  ordW n [x, y] r && ordW n (commWord x y mx my) s

@[expose] def countProducts (n : Nat) (f : Table → Bool) : List (List Table) → Table → Nat
  | [], g => if f g then 1 else 0
  | T :: Ts, g => T.foldl (fun c t => c + countProducts n f Ts (compT n g t)) 0

@[expose] def filterProducts (n : Nat) (f : Table → Bool) :
    List (List Table) → Table → List Table → List Table
  | [], g, acc => if f g then g :: acc else acc
  | T :: Ts, g, acc => T.foldl (fun acc t => filterProducts n f Ts (compT n g t) acc) acc

@[expose] def pairCount (X Y : List Table) (r : Table → Table → Bool) : Nat :=
  X.foldl (fun c x => c + Y.countP (r x)) 0

end CFSG.Sporadic.Schreier.Native
