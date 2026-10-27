module

public import Certificates.Data.SmithL6Stab

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

@[expose] def prOrd3 : Bool :=
  (List.range 1953).all fun x => tvImg 0 (tvImg 31 (tvImg 0 (tvImg 31 (tvImg 0 (tvImg 31 x))))) == x

@[expose] def prChkStd : Bool :=
  tvPair 0 == (1, 2) && tvPair 31 == (2, 1) && stabRep 6 == 31 && prOrd3

@[expose] def prOrd4 (a : Nat) : Bool :=
  (List.range 1953).all fun x =>
    tvImg 0 (tvImg a (tvImg 0 (tvImg a (tvImg 0 (tvImg a (tvImg 0 (tvImg a x))))))) == x

@[expose] def prChkOrd4 : Bool :=
  (List.range 1953).all fun a => stabCls a == 6 || prOrd4 a

@[expose] def prU (k : Nat) : Nat := ((List.range 64).find? fun u => form (tvPair k).2 u).getD 0

@[expose] def prW (k : Nat) : Nat := wedge3 1 2 (tvPair k).1

@[expose] def prC (k : Nat) : Nat := wedge3 1 2 (prU k)

@[expose] def prIdx (k : Nat) : Nat := ((List.range 1395).find? fun i => wt i == prW k).getD 1395

@[expose] def prChkF3 : Bool :=
  (List.range 1953).all fun k =>
    !(tvImg k 0 == 0 && tvImg k 31 == 31) ||
      (decide (prIdx k < 1395) && decide (prC k < 2 ^ 20) &&
        applyCols (tvCols k) (prC k) ^^^ prC k == wt (prIdx k) &&
        applyCols (tvCols 0) (wt (prIdx k)) == wt (prIdx k) &&
        applyCols (tvCols 31) (wt (prIdx k)) == wt (prIdx k))

end CFSG.SmithL6
