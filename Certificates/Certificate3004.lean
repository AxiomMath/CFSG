module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import Certificates.Data.CFSGNative.Fischer.Polar
import Certificates.Kernel.UnitarySix.Polar

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier
    CFSG.Fischer.Native in
theorem certificate3004 : 
      aGens.all (fun g => (List.range 21).any fun i =>
        tblEq 693 (toTable g) tvTabs[beta[i]!]!) = true ∧
      tblEq 693 (toTable j1) tvTabs[beta[5]!]! = true := KernelU6.cert3004

end Certificates
