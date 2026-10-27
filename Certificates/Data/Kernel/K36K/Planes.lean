module

public import Certificates.Data.Kernel.CoreD2K.Check
public import Certificates.Data.Kernel.K36K.Check

public section

namespace CFSG.KS.K36K

open Certificates.CoreD2Perm Certificates.K36Spor

@[expose] def vOf (S : SData) : VData :=
  { base := S.base, ys := S.ys, gk := [], wAs := S.wAs, wBs := S.wBs }

end CFSG.KS.K36K

end
