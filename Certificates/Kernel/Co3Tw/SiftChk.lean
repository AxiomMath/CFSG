module

public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Kernel.Co3Tw.SrchChk
public import Certificates.Kernel.Co3Tw.PairsData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.KC.Enum CFSG.KS CFSG.KC.PermWit CertificateChecks.KernelSpor

@[expose] noncomputable def siftC (c : Nat) : Bool :=
  siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (fld(PD.cc, Nat.mul (nat_lit 2484) c, mask (nat_lit 2484)))

#kc_each CertificateChecks.KernelCo3Tw ch431008sc_ siftC 0 173

theorem ch431008sd : allN 7 (fun k => bAnd(siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (xpK k),
    siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (ypK k))) = true := by quickRfl

end CertificateChecks.KernelCo3Tw

end
