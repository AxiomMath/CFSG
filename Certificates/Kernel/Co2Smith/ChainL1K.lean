module

public import Certificates.Kernel.Co2Smith.ChainL1Data
public import Certificates.Kernel.Co2Smith.Psi
public import Certificates.Kernel.Co2Smith.CentK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Smith.Native

theorem chL1Bind_k : allN 22 (fun i => (u62L1Words.getD i []).all (· < 22) &&
    bindVK (KernelSporSch.Co2M.PV 0) (L1GP i) (trK 22 (wK LP (u62L1Words.getD i [])))) = true := by
  decide +kernel

theorem chL1O_k : allN 22 (fun i =>
    Nat.beq (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (L1GP i)) CIK) (CL1.S i)) = true := by
  decide +kernel

theorem l1Cent_k : allN 22 (fun i =>
    permOK 2300 12 (mask 12) (2300 * 12) (CL1.S i) (CL1.SI i) && siftP (CL1.S i) &&
    Nat.beq (pcomp 2300 12 (mask 12) (CL1.S i) (XW 0))
      (pcomp 2300 12 (mask 12) (XW 0) (CL1.S i)) &&
    Nat.beq (pg 12 (mask 12) (CL1.S i) 0) 0) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
