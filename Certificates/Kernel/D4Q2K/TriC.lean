module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.DataC
public import Certificates.Kernel.D4Q2K.DataS
public import Certificates.Kernel.D4Q2K.DataT
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

@[expose] noncomputable def triCSl (s : Nat) : Bool := triCK DS.SF DT.TF DC.cl (Nat.mul 20 s) 20

#kc_each CertificateChecks.KernelD4Q2K.triCSl 0 112

theorem triC_negRow :
    (!triCK DS.SF (fun j => Nat.land (DT.TF j) (Nat.sub (Nat.shiftLeft 1 4480) 2)) DC.cl 0 20) =
      true := by
  quickRfl

theorem triC_negCol : (!triCK (fun i => DS.SF (Nat.succ i)) DT.TF DC.cl 0 1) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end
