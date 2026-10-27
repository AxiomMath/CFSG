module

public import Certificates.Kernel.Co1Planes.Data
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.Co1Planes
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Planes

open CFSG.KS.SporSch.M24 CFSG.KC.Co1Planes CFSG.RankThree.PartOne.SPOR CFSG.KD.Co1B

theorem kDA : dagWK DA.M DA.MI 4 49 CP.KWA = true := by quickRfl
theorem kDC : dagWK DC.M DC.MI 4 39 CP.KWC = true := by quickRfl
theorem kDB : dagWK DB.M DB.MI 4 57 CP.KWB = true := by quickRfl

theorem kBA : (Nat.beq (DA.M 0) SA && Nat.beq (DA.M 1) SB &&
    Nat.beq (DA.M 2) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 23) &&
    Nat.beq (DA.M 3) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 51)) = true := by quickRfl
theorem kBC : (Nat.beq (DC.M 0) SA && Nat.beq (DC.M 1) SB &&
    Nat.beq (DC.M 2) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 23) &&
    Nat.beq (DC.M 3) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 51)) = true := by quickRfl
theorem kBB : (Nat.beq (DB.M 0) SA && Nat.beq (DB.M 1) SB &&
    Nat.beq (DB.M 2) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 23) &&
    Nat.beq (DB.M 3) (CFSG.KC.Co1F2.getL CFSG.KC.Co1B.oneK IRS 51)) = true := by quickRfl

theorem kWA : CP.KWA.map CFSG.Sporadic.Co1Schreier.Native.decWord = co1PlaneADerivs := by
  decide +kernel
theorem kWC : CP.KWC.map CFSG.Sporadic.Co1Schreier.Native.decWord = co1PlaneCDerivs := by
  decide +kernel
theorem kWB : CP.KWB.map CFSG.Sporadic.Co1Schreier.Native.decWord = co1PlaneBDerivs := by
  decide +kernel

theorem kA : classK DA.M DA.MI 49 co1PlaneA = true := by quickRfl
theorem kC : classK DC.M DC.MI 39 co1PlaneC = true := by quickRfl
theorem kB : classK DB.M DB.MI 57 co1PlaneB = true := by quickRfl

end CertificateChecks.KernelCo1Planes

end
