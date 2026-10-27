module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
public import Certificates.Kernel.D4Q2K.DataC
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

@[expose] noncomputable def cqSl (s : Nat) : Bool := cliqueK D.RF D.MF DC.cl (Nat.mul 20 s) 20

#kc_each CertificateChecks.KernelD4Q2K.cqSl 0 112

theorem cqSl_negDrop :
    (!cliqueN D.RF D.MF 1 0 [(DC.cl.headD []).tail]) = true := by
  quickRfl

theorem cqSl_negRow : (!cliqueN (fun i => D.RF (Nat.succ i)) D.MF 1 0 DC.cl) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end
