
module


public import CFSG.Sporadic.Schreier.ONCheckChainInputs
import Certificates.Kernel.Sporadic.ON.Order2212

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native in
theorem certificate2212 : pointChainOK CFSG.Sporadic.ON.Native.nPts 2 qonStrongArrs Data.baseList.toArray Data.strongWords 4 = true ∧
    cOrbitSizes CFSG.Sporadic.ON.Native.nPts qonStrongArrs Data.baseList.toArray =
      [245520, 52136, 36] ++ List.replicate 26 1 := KernelSpor.ON.facts2212

end Certificates
