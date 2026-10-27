module

public import Certificates.Data.Kernel.Sp43K
public import Certificates.Data.Sp43.Code

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43.Native

@[expose] def digT (t k : Nat) : Nat :=
  if t.testBit k then 1 else if t.testBit (k + 16) then 2 else 0

@[expose] def toCT (t : Nat) : Nat := horner ((List.range 16).map (digT t))

@[expose] def spT (t : Nat) : Bool :=
  let c := toCT t
  let r0 := c % 81
  let r1 := c / 81 % 81
  let r2 := c / 6561 % 81
  let r3 := c / 531441 % 81
  omg r2 r3 == 0 && omg r1 r2 == 0 && omg r1 r3 == 2 && omg r0 r1 == 0 && omg r0 r2 == 2 &&
    omg r0 r3 == 0

end CFSG.KC.Sp43K

end
