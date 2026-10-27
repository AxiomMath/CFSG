module

public import CFSG.Sporadic.Schreier.ONCheckSmallInputs
import Certificates.Kernel.Sporadic.ON6.Final

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native in
theorem certificate2215 : smallChainOK 32 Data.T32Chain = true ∧ smallChainOK 120 Data.M120Chain = true ∧
    smallChainOK 120 Data.L120Chain = true ∧ smallChainOK 21 Data.PSL21Chain = true ∧
    smallChainOK 120 Data.PSL120Chain = true ∧
    cOrbitSizes 32 Data.T32Chain.strongGenerators Data.T32Chain.base = [32, 8, 2] ∧
    cOrbitSizes 120 Data.M120Chain.strongGenerators Data.M120Chain.base = [120, 56, 6] ∧
    cOrbitSizes 120 Data.L120Chain.strongGenerators Data.L120Chain.base = [120, 56, 3] ∧
    cOrbitSizes 21 Data.PSL21Chain.strongGenerators Data.PSL21Chain.base = [21, 20, 16, 3] ∧
    cOrbitSizes 120 Data.PSL120Chain.strongGenerators Data.PSL120Chain.base =
      [120, 21, 8] := KernelSpor.ON6K.facts2215

end Certificates
