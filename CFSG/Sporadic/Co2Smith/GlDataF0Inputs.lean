module

public import CFSG.Sporadic.Co2Smith.GlDataRootInputs

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def glHRows (k : Nat) : Array Nat :=
  if k == 1 then glD1h else if k == 2 then mulRows 22 glD0h glD1h
  else if k == 4 then mulRows 22 glD1h glW1 else mulRows 22 (mulRows 22 glD0h glD1h) glW1

@[expose] def glHR : Array (Array Nat) := hRows CFSG.Sporadic.Co2Smith.seedRowsArr

@[expose] def glQRows (e : Nat) : Array Nat :=
  nfRows CFSG.Sporadic.Co2Smith.seedRowsArr glHR (e / 256) (e % 256)

@[expose] def glF0Conj (h h' : Array Nat) (e : Nat) : Array Nat :=
  mulRows 22 (mulRows 22 h (glQRows e)) h'

@[expose] def glFixZ (Y : Array Nat) : Bool := mulRows 22 Y (subId glZ) == subId glZ

@[expose] def glF0Root (k : Nat) : Nat :=
  if k == 1 then 0 else if k == 2 then 1 else if k == 4 then 3 else 2

@[expose] def glF0Valid (Y : Array Nat) : Bool :=
  validM (mulRows 22 Y glZ) && validM (mulRows 22 glZ Y) && validM (mulRows 22 Y (subId glZ))

@[expose] def glF0kOK (k : Nat) (h h' : Array Nat) : Bool :=
  ((List.range 512).filter fun e => commRows (glF0Conj h h' e) glZ).length == 128 &&
    ((List.range 512).filter fun e =>
      commRows (glF0Conj h h' e) glZ && glFixZ (glF0Conj h h' e)).length == 4 &&
    (List.range 512).all (fun e => glF0Valid (glF0Conj h h' e)) &&
    mulRows 22 h h' == idRows 22 &&
    ([1, 2, 3].all fun t =>
      let Y := mulRows 22 (mulRows 22 h' (glRootRows (glF0Root k) t)) h
      commRows Y glZ && glFixZ Y) &&
    [0, 1, 2, 3].all fun s => validM (glRootRows (glF0Root k) s) && [0, 1, 2, 3].all fun t =>
      s == t || glRootRows (glF0Root k) s != glRootRows (glF0Root k) t

@[expose] def glF0OK : Bool :=
  validM (subId glZ) && [1, 2, 4, 5].all fun k => glF0kOK k (glHRows k) (glFrameConjRows k)

end CFSG.Sporadic.Co2Smith.Native
