module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
import Certificates.Kernel.UnitarySix.Fischer

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.Hunt CFSG.Sporadic.Schreier CFSG.EvenSmallLie.UnitarySix
    CFSG.Fischer.Native in
theorem certificate3181 : 
      (braidOK tvTabs = true)
    ∧ (toTable j1 = tvTabs[(0 : Fin 693).val]!) := KernelU6.cert3181

end Certificates
