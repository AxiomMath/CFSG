module

public section

namespace CFSG.KC.Sp43K

@[expose] def laneT : Nat := 65535

@[expose] def oneT : Nat := 33825

@[expose] def colT (x k : Nat) : Nat :=
  let y := (x >>> k) &&& 4369
  y ||| (y <<< 1) ||| (y <<< 2) ||| (y <<< 3)

@[expose] def rowT (x k : Nat) : Nat :=
  let z := (x >>> (4 * k)) &&& 15
  z ||| (z <<< 4) ||| (z <<< 8) ||| (z <<< 12)

@[expose] def mul3P (ap am bp bm : Nat) : Nat := (ap &&& bp) ||| (am &&& bm)

@[expose] def mul3M (ap am bp bm : Nat) : Nat := (ap &&& bm) ||| (am &&& bp)

@[expose] def add3P (ap am bp bm : Nat) : Nat :=
  ((laneT ^^^ (ap ||| am)) &&& bp) ||| (ap &&& (laneT ^^^ (bp ||| bm))) ||| (am &&& bm)

@[expose] def add3M (ap am bp bm : Nat) : Nat :=
  ((laneT ^^^ (ap ||| am)) &&& bm) ||| (am &&& (laneT ^^^ (bp ||| bm))) ||| (ap &&& bp)

@[expose] def termP (a b k : Nat) : Nat :=
  mul3P (colT (a &&& laneT) k) (colT (a >>> 16) k) (rowT (b &&& laneT) k) (rowT (b >>> 16) k)

@[expose] def termM (a b k : Nat) : Nat :=
  mul3M (colT (a &&& laneT) k) (colT (a >>> 16) k) (rowT (b &&& laneT) k) (rowT (b >>> 16) k)

@[expose] def s1P (a b : Nat) : Nat := add3P (termP a b 0) (termM a b 0) (termP a b 1) (termM a b 1)

@[expose] def s1M (a b : Nat) : Nat := add3M (termP a b 0) (termM a b 0) (termP a b 1) (termM a b 1)

@[expose] def s2P (a b : Nat) : Nat := add3P (s1P a b) (s1M a b) (termP a b 2) (termM a b 2)

@[expose] def s2M (a b : Nat) : Nat := add3M (s1P a b) (s1M a b) (termP a b 2) (termM a b 2)

@[expose] def s3P (a b : Nat) : Nat := add3P (s2P a b) (s2M a b) (termP a b 3) (termM a b 3)

@[expose] def s3M (a b : Nat) : Nat := add3M (s2P a b) (s2M a b) (termP a b 3) (termM a b 3)

@[expose] def mulT (a b : Nat) : Nat := (s3P a b &&& laneT) ||| (s3M a b <<< 16)

end CFSG.KC.Sp43K

end
