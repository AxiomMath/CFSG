module

public import Certificates.Kernel.Co2Smith.CentData
public import Certificates.Kernel.SporSch.Co2M.WordsBase
public import Certificates.Kernel.Sporadic.Co2.ChainAD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def siftP (G : Nat) : Bool :=
  siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR KernelSpor.Co2A.TRI
    KernelSpor.Co2A.BP 6 0 G

theorem xw_k : (permOK 2300 12 (mask 12) (2300 * 12) (XW 0) (XW 1) &&
    permOK 2300 12 (mask 12) (2300 * 12) (XW 2) (XW 3) && siftP (XW 0) && siftP (XW 2) &&
    Nat.beq (pcomp 2300 12 (mask 12) (XW 0) (XW 2)) (pcomp 2300 12 (mask 12) (XW 2) (KernelSporSch.Co2M.WE 0))) =
    true := by
  decide +kernel

theorem tz_k : allN 28 (fun k => permOK 2300 12 (mask 12) (2300 * 12) (TZ k) (TZ (28 + k)) &&
    siftP (TZ k) &&
    Nat.beq (pcomp 2300 12 (mask 12) (TZ k) (XW 0)) (pcomp 2300 12 (mask 12) (XW 0) (TZ k)) &&
    allN k (fun j => !Nat.beq (pg 12 (mask 12) (TZ k) 0) (pg 12 (mask 12) (TZ j) 0))) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Smith
