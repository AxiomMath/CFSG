module

public import CFSG.Quasithin.H13.AS91Sec4ThreeInputs
import Certificates.Kernel.AS91I43.Checks
import CFSG.Certificates.Kernel.AS91I43Sound

public section

namespace Certificates

open CertificateChecks.KernelAS91I43 in
open CFSG.Quasithin.H13.AS91 in
theorem certificate89403 : Two.iOK43 () = true :=
  Certificates.Kernel.AS91I43.iOK43_of ch89403_cnt ch89403_w0 ch89403_w1 ch89403_w2 ch89403_w3
    ch89403_w4 ch89403_w5 ch89403_w6 ch89403_w7 ch89403_inter

end Certificates
