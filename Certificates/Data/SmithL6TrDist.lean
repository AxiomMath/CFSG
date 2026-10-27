module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

@[expose] def trChkDist2 : Bool :=
  (List.range 1395).all fun i =>
    ((List.range 1395).filter fun j => meetCard i j == 1).length == 784

end CFSG.SmithL6
