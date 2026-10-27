
module

public import CFSG.Sporadic.Schreier.ONCheckChainBase

public import CFSG.Sporadic.Schreier.ONActionData
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.Schreier.ONCheckChainInputs
public import Certificates.Certificate2212
public import Certificates.Certificate2212Base

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

theorem qon_chain_cert :
    pointChainOK nPts 2 qonStrongArrs Data.baseList.toArray Data.strongWords 4 = true ∧
      cOrbitSizes nPts qonStrongArrs Data.baseList.toArray =
        [245520, 52136, 36] ++ List.replicate 26 1 :=
  Certificates.certificate2212

end CFSG.ONSchreier
