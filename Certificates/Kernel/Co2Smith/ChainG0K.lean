module

public import Certificates.Kernel.Co2Smith.ChainG0Data
public import Certificates.Kernel.Co2Smith.Psi

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def rtPsi (k : Nat) : Nat :=
  pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (RTP k)) CIK

@[expose] noncomputable def rtM (k : Nat) : Nat := if k < 42 then rootK (rtR k) (rtT k) else gaK

theorem chG0Bind_k : allN 13 (fun i => (glG0Words.getD i []).all (· < 22) &&
    bindVK (KernelSporSch.Co2M.PV 0) (G0GP i) (trK 22 (wK LP (glG0Words.getD i []))) &&
    mapsK (wK LP (glG0Words.getD i [])) 80 80) = true := by
  decide +kernel

theorem chG0O_k : allN 13 (fun i =>
    Nat.beq (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (G0GP i)) CIK) (CG0.S i)) = true := by
  decide +kernel

theorem rtBind_k : allN 43 (fun k =>
    bindVK (KernelSporSch.Co2M.PV 0) (RTP k) (trK 22 (rtM k)) &&
    allN 2300 (fun i => Nat.blt (pg 12 (mask 12) (rtPsi k) i) 2300)) = true := by
  decide +kernel

theorem rtSift_k : allN 42 (fun k =>
    siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.LR CG0.TRI CG0.BP 5 0 (rtPsi k)) &&
    !siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) CG0.LR CG0.TRI CG0.BP 5 0 (rtPsi 42) &&
    Nat.beq (Nat.shiftRight (rtPsi 42) (2300 * 12)) 0 = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
