module

public import Certificates.Data.Kernel.SmithL6K

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def pEdgeK (P : List Nat) (s u v : Nat) : Bool := fldW 11 (P.getD s 0) u == v

@[expose] def row0K (W M : Nat) : Bool :=
  (List.range 1395).all fun j =>
    fB (fldW 20 W 0) (fldW 20 W j) == (fldW 64 M 0 &&& fldW 64 M j == 1)

end CFSG.SmithL6.K
