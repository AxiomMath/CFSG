module

public import Certificates.Kernel.Co1SevenK.Dag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.Co1SevenK.Dag
public import Certificates.Kernel.SporSch.Co1.GenBfs
public import Certificates.Kernel.Sporadic.OrbRecGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Seven

meta def sylG : Array Rows := #[rowAt dagD.1 iS, rowAt dagD.1 iT]

meta def sylC : Array Nat :=
  (CFSG.Sporadic.Co1.TwoBNative.gtBFS sylG 100000).pts.map fun p =>
    ((List.range 48).find? fun c => p == pow (xGen dagD.1 (c / 6)) (c % 6 + 1)).getD 48

end CertificateChecks.KernelCo1SevenK

#kss_co1gt CertificateChecks.KernelCo1SevenK.PT CertificateChecks.KernelCo1SevenK.sylG 100000

#kc_nattree CertificateChecks.KernelCo1SevenK.PC CertificateChecks.KernelCo1SevenK.sylC

end
