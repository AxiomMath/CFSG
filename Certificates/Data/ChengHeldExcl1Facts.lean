module

public import Certificates.Data.ChengHeldSec2Facts

public section

namespace CFSG.OddStandard.ChengHeldData

open RegModel

@[expose] def exclXiM (M : RegModel) : Bool :=
  let W := M.cent (secV M)
  let Zt := secZ M
  (elems W).all fun w => M.m w (M.g 6) != M.m (M.g 6) w || Zt[M.m w w]!

@[noinline, expose] def chExcl1OK : Bool := [0, 1].all fun α => exclXiM (mkReg α)

end CFSG.OddStandard.ChengHeldData
