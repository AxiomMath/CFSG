module

public import Certificates.Data.CFSGNative.ReflExt.Check

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose, reducible] def e6Row (i : Nat) : Vec :=
  (List.range 6).map fun j =>
    if i = j then 2
    else if [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)].any (fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)) then 2
    else 0

@[expose, reducible] def e6Frame (D s : Nat) : Pt := mkFrame 3 6 D e6Row s [1, 0, 2, 0, 1, 2] 1360488960

@[expose] def e6Check (_ : Unit := ()) : Bool :=
  checkFrame (e6Frame 6 0) && checkFrame (e6Frame 7 1) && checkFrame (e6Frame 7 0)

end CFSG.ReflExt

end
