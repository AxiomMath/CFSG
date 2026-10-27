module

public import CFSG.Monster.GMS.S365Facts
public import CFSG.Monster.GMS.Leech.Linear
public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Monster.Tri.ASegFactsCo1WInputs
public import Certificates.Kernel.Co1M.Orb98280
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.OddFacts
public import Certificates.Certificate10073Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KC.VecK CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Monster.Tri

theorem inO46 (w : Nat) :
    inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
  cm_orb_inPts w

theorem tyLab46 (w : Nat) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      if w = 0 then 0 else if q0N w then 2 else
        if orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 w then 3 else 1 := by
  unfold tyLab
  rw [inO46]

theorem wCheck_true : wCheck = true := by
  unfold wCheck
  simp only [tyLab46]
  quickRfl

theorem baseCheck_true : baseCheck = true := by
  unfold baseCheck
  simp only [tyLab46]
  quickRfl

end CertificateChecks.KernelCo1M

end
