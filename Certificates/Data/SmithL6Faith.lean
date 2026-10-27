module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

@[expose] def chkTvArrInj : Bool :=
  (List.range 1953).all fun b => (List.range b).all fun a => tvArr[a]! != tvArr[b]!

end CFSG.SmithL6
