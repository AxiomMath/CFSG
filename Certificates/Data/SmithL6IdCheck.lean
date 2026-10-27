module

public import Certificates.Data.SmithL6Check
public import Certificates.Data.SmithECheck

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

@[expose] def idChkWt : Bool :=
  (List.range 1395).all fun i => decide (wtArr[i]! < 2 ^ 20) && wtArr[i]! != 0

@[expose] def idChkWtInj : Bool :=
  (List.range 1395).all fun i => (List.range 1395).all fun j => i == j || wtArr[i]! != wtArr[j]!

end CFSG.SmithL6
