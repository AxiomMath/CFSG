module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glQtD0 : Array Nat := glR [11, 12]

@[expose] def glQtGens : Array (Array Nat) :=
  Array.ofFn (n := 7) fun k => if k.val < 6 then glMkGens[k.val]! else glMkR[16]!

@[expose] def glQtLetters : List (Nat × List Nat) :=
  [(11, [0, 3]), (12, [2, 3, 4, 3, 2, 1, 5, 4]), (13, [0, 1, 3, 4, 6, 1, 5, 6])]

@[expose] def glQtOK : Bool :=
  commRows glQtD0 glZ &&
    (List.range 36).all (fun k => commRows glQtD0 glMkR[k]! == (k == 0 || k == 16 || k == 18)) &&
    mulRows 22 (mulRows 22 glZ glMkR[16]!) glZ == glMkR[18]! &&
    glQtLetters.all (fun e => e.2.all (· < 7) && wRows glQtGens e.2 == glR [e.1]) &&
    glMkFixIs (mulRows 22 glGa glZ) 52

end CFSG.Sporadic.Co2Smith.Native
