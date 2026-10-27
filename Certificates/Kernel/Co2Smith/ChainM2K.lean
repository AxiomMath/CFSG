module

public import Certificates.Kernel.Co2Smith.ChainM2Data
public import Certificates.Kernel.Co2Smith.Psi

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Smith.Native

theorem chM2Bind_k : allN 3 (fun i => (glM2Words.getD i []).all (· < 22) &&
    bindVK (KernelSporSch.Co2M.PV 0) (M2GP i) (trK 22 (wK LP (glM2Words.getD i [])))) = true := by
  decide +kernel

theorem chM2O_k : allN 3 (fun i =>
    Nat.beq (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (M2GP i)) CIK) (CM2.S i)) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
