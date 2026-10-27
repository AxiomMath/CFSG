module

public import Certificates.Kernel.Co3Tw.PairsData
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KS

theorem ch431008cp : allN 173 (fun c => CFSG.KC.Misc.ArrEnum.permB 276 9
    (fld(PD.cc, Nat.mul (nat_lit 2484) c, mask (nat_lit 2484)))) = true := by quickRfl

theorem neg431008cp : (!CFSG.KC.Misc.ArrEnum.permB 276 9 0) = true := by quickRfl

end CertificateChecks.KernelCo3Tw

end
