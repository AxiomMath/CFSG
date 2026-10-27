module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.GMS.Facts.Co1Local
public import CFSG.Monster.GMS.S365NativeInputs
public import Certificates.Kernel.Co1M.Orb98280
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

namespace CertificateChecks.KernelCo1M

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.SmallF2.Native
  CFSG.KC.Co1M CFSG.KC.VecK CFSG.Monster.GMS.S365

@[expose] noncomputable def labK (w : Nat) : Nat :=
  if w = 0 then 0 else if q0N w then 2
  else if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w then 3 else 1

theorem tyLab_eq_labK :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 = labK := by
  funext w
  have e : Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  rw [tyLab, labK, e]

theorem c10043_eight : eightCheck = true := by
  unfold eightCheck
  dsimp only
  rw [tyLab_eq_labK]
  quickRfl

theorem c10043_neg :
    (!orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 24 &&
      !orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 1 &&
      !(labK 24 == 3) && labK 24 == 1) = true := by
  quickRfl

open Certificates in
open CFSG.Monster.GMS.S365 in
theorem c10043 :
    eightCheck = true := c10043_eight

end CertificateChecks.KernelCo1M

end
