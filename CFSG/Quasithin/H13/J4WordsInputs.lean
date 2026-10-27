module

public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.H13.J4Elems
public meta import Certificates.Data.CFSGNative.J4.Cert

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native

@[expose] def tChecks : Bool :=
  let uv := uvPairsOf basePairs
  let tP := tOf uv
  eqRows (mulRows tP.1 (uv[0]?.getD prOne).1) (mulRows (uv[0]?.getD prOne).1 tP.1) &&
    eqRows (mulRows tP.1 (uv[1]?.getD prOne).1) (mulRows (uv[1]?.getD prOne).1 tP.1) &&
    eqRows (mulRows tP.1 tP.1) idRows && rowsNe tP.1 idRows

end CFSG.Quasithin.H13.J4
