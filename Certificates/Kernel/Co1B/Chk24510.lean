module

public import Certificates.Kernel.Co1B.Dag24510
public import Certificates.Kernel.Co1B.Dag2044
public import Certificates.Kernel.Co1B.IotaData
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.Co1BW
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.H24510

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KC.Co1F2 CFSG.KD.Co1B
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CFSG.Sporadic.Co1Block
open CFSG.KC.Co1B (mulWK)

theorem kPb : allN twoABray.length (fun i => Nat.beq (PA.M i) (C2044.D2.M i)) = true := by
  quickRfl
theorem kP : dagIK PA.M PA.MI twoABray.length PA.N perfPA = true := by quickRfl
theorem kpi : perfPIdxA.all (fun j => decide (j < PA.N)) = true := by quickRfl
theorem kUb : allN perfPIdxA.length (fun l => Nat.beq (UA.M l) (PA.M (perfPIdxA.getD l 0))) =
    true := by quickRfl
theorem kU : dagIK UA.M UA.MI perfPIdxA.length UA.N perfUA = true := by quickRfl
theorem kci : perfCIdxA.all (fun ij => decide (ij.1 < UA.N) && decide (ij.2 < UA.N)) = true := by
  quickRfl
theorem kFb : allN perfCIdxA.length (fun j => Nat.beq (FA.M j)
    (mulWK (mulWK (UA.MI (perfCIdxA.getD j (0, 0)).1) (UA.MI (perfCIdxA.getD j (0, 0)).2))
      (mulWK (UA.M (perfCIdxA.getD j (0, 0)).1) (UA.M (perfCIdxA.getD j (0, 0)).2)))) = true := by
  quickRfl
theorem kF : dagIK FA.M FA.MI perfCIdxA.length FA.N perfFA = true := by quickRfl
theorem kfi : perfFIdxA.all (fun j => decide (j < FA.N)) = true := by quickRfl
theorem kf : allN perfPIdxA.length
    (fun l => Nat.beq (FA.M (perfFIdxA.getD l 0)) (PA.M (perfPIdxA.getD l 0))) = true := by
  quickRfl
theorem kQb : allN perfPIdxA.length (fun l => Nat.beq (QA.M l) (PA.M (perfPIdxA.getD l 0))) =
    true := by quickRfl
theorem kQ : dagIK QA.M QA.MI perfPIdxA.length QA.N perfQA = true := by quickRfl
theorem kqi : perfQIdxA.all (fun j => decide (j < QA.N)) = true := by quickRfl
theorem kq : allN perfQIdxA.length (fun l => Nat.beq (QA.M (perfQIdxA.getD l 0))
    (getL CFSG.KC.Co1B.oneK IRS (36 + l))) = true := by quickRfl

end CertificateChecks.KernelCo1B.H24510

end
