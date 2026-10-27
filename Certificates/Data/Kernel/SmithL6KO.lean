module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll
public import Certificates.Data.SmithL6Orbit

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def meetK (M j : Nat) : Nat :=
  ((List.range 64).countP (fun x => (fldW 64 M 0 &&& fldW 64 M j).testBit x) - 1) ^ 2

@[expose] def dRootK (M c : Nat) : Nat := ((List.range 1395).find? fun j => meetK M j == c).getD 0

@[expose] def oEdgeK (W M : Nat) (G : List (List Nat)) (s u v : Nat) : Bool :=
  fldW 20 W v == apK (G.getD s []) (fldW 20 W u) && meetK M u == meetK M v

@[expose] def s2AK (S : Nat) : Bool :=
  (List.range 49).all fun k => (List.range 49).all fun l => k == l || S.testBit (uco[k]! ^^^ uco[l]!)

@[expose] def s2BK (S : Nat) (Wt : List (Nat × Nat)) : Bool :=
  (List.range 512).all fun v => !S.testBit v || (let w := Wt.getD v (0, 0)
    decide (w.1 < 49) && decide (w.2 < 49) && w.1 != w.2 && uco[w.1]! ^^^ uco[w.2]! == v)

@[expose] def uClsK (S v : Nat) : Nat :=
  if v == 0 then 0 else if ptMask.testBit v then 1 else if S.testBit v then 2 else 3

@[expose] def uRootK (S c : Nat) : Nat := ((List.range 512).find? fun v => uClsK S v == c).getD 0

@[expose] def uEdgeK (S : Nat) (U : List (List Nat)) (s u v : Nat) : Bool :=
  uClsK S u == uClsK S v && apK (U.getD s []) u == v

@[expose] def p0K (C M A : Nat) : List Nat :=
  (List.range 1953).filter fun a => M.testBit (fldW 12 C a / 64) && A.testBit (fldW 12 C a % 64)

@[expose] def ucolsK (C I : Nat) (P : List Nat) (p : Nat) : List Nat :=
  (List.range 9).map fun j => uco[P.findIdx (· == tvImgP C I p ugens[j]!)]!

end CFSG.SmithL6.K
