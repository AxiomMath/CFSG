
module


public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.AllConj

open CFSG.Sporadic.Th.Native

end CFSG.Sporadic.Th.Max3.AllConj

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

end CFSG.Sporadic.Th.Max3

namespace CFSG.Sporadic.Th.Max3.AllConj

open CFSG.Sporadic.Th.Native

@[expose] def rowsFusionQ0 : Array V4 :=
  fusionRows (abRows fusionWordQ0) (abRows (invWord fusionWordQ0)) (rowsQ 0)

end CFSG.Sporadic.Th.Max3.AllConj
