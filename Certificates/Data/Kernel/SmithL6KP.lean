module

public import Certificates.Data.Kernel.SmithL6K

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def twoB (x : Nat) : Bool := x != 1 && !atLeast4 x

@[expose] def dist2K (l rows : List Nat) : Bool :=
  rows.all fun a => (l.countP fun b => twoB (a &&& b)) == 784

end CFSG.SmithL6.K
