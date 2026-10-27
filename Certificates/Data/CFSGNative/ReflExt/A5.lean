module

public import Certificates.Data.CFSGNative.ReflExt.Check

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose, reducible] def a5Row (i : Nat) : Vec :=
  (List.range 5).map fun j => if i = j then 2 else if i + 1 = j ∨ j + 1 = i then 2 else 0

@[expose, reducible] def a5Frame (D : Nat) : Pt := mkFrame 3 5 D a5Row 1 [1, 2, 0, 1, 2] 6298560

@[expose] def a5Check (_ : Unit := ()) : Bool := checkFrame (a5Frame 5) && checkFrame (a5Frame 6)

end CFSG.ReflExt

end
