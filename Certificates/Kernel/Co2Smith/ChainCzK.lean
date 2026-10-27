module

public import Certificates.Kernel.Co2Smith.ChainCzData
public import Certificates.Kernel.Co2Smith.Psi
public import Certificates.Kernel.Co2Smith.CentK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Smith.Native

theorem chCzBind_k : allN 21 (fun i => (glCzWords.getD i []).all (· < 22) &&
    bindVK (KernelSporSch.Co2M.PV 0) (CzGP i) (trK 22 (wK LP (glCzWords.getD i [])))) = true := by
  decide +kernel

theorem chCzO_k : allN 21 (fun i =>
    Nat.beq (pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (CzGP i)) CIK) (CCz.S i)) = true := by
  decide +kernel

theorem czCent_k : allN 21 (fun i =>
    permOK 2300 12 (mask 12) (2300 * 12) (CCz.S i) (CCz.SI i) && siftP (CCz.S i) &&
    Nat.beq (pcomp 2300 12 (mask 12) (CCz.S i) (XW 0))
      (pcomp 2300 12 (mask 12) (XW 0) (CCz.S i))) = true := by
  decide +kernel

theorem czMaps_k : glCzLetters.all (fun k => decide (k < 22) && mapsK (wK LP [k]) 80 80) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
