module

public import CFSG.Sporadic.Schreier.ONOuterData
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Sporadic.Schreier.ONOuterData
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.Schreier.ONCheckSmallInputs
public import Certificates.Certificate2215

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native

theorem small_chain_certs :
    smallChainOK 32 Data.T32Chain = true ∧ smallChainOK 120 Data.M120Chain = true ∧
      smallChainOK 120 Data.L120Chain = true ∧ smallChainOK 21 Data.PSL21Chain = true ∧
      smallChainOK 120 Data.PSL120Chain = true ∧
      cOrbitSizes 32 Data.T32Chain.strongGenerators Data.T32Chain.base = [32, 8, 2] ∧
      cOrbitSizes 120 Data.M120Chain.strongGenerators Data.M120Chain.base = [120, 56, 6] ∧
      cOrbitSizes 120 Data.L120Chain.strongGenerators Data.L120Chain.base = [120, 56, 3] ∧
      cOrbitSizes 21 Data.PSL21Chain.strongGenerators Data.PSL21Chain.base = [21, 20, 16, 3] ∧
      cOrbitSizes 120 Data.PSL120Chain.strongGenerators Data.PSL120Chain.base =
        [120, 21, 8] :=
  Certificates.certificate2215

end CFSG.ONSchreier
