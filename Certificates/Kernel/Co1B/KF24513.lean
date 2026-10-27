module

public import Certificates.Kernel.Co1B.Dag2045
public import Certificates.Kernel.Co1B.Bfs24513
public import Certificates.Data.Kernel.Co1BW
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KC.Enum CFSG.KC.Co1B CFSG.KS.Raw

theorem kF : allN 32768 (fun i => strictB (mulWK (ST.P i) (ST.P i)) fun s =>
    unpack 24 24 (mulWK s s) != unpack 24 24 (Cent2045.D1.M 0)) = true := by quickRfl

end CertificateChecks.KernelCo1B.Syl2B

end
