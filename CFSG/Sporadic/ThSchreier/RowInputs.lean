
module

public import CFSG.Sporadic.Th.BaseBase
public import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.ThSchreier.Text
public meta import Certificates.Data.CFSGNative.Th.Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Matrix Pointwise

@[expose] def formInvRows : Array V4 := invRows fcRows

end CFSG.Sporadic.ThSchreier
