module

public import Certificates.Kernel.Co2Smith.ChainNData
public import Certificates.Kernel.Co2Smith.Psi

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Smith.Native

theorem chNBind_k : allN 11 (fun i => (glNWords.getD i []).all (· < 22) &&
    bindVK (KernelSporSch.Co2M.PV 0) (NGP i) (trK 22 (wK LP (glNWords.getD i [])))) = true := by
  decide +kernel

theorem chNO_k : allN 11 (fun i =>
    Nat.beq (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (NGP i)) CIK) (CN.S i)) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
