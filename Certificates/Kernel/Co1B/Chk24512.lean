module

public import Certificates.Kernel.Co1B.Dag24512
public import Certificates.Kernel.Co1B.Dag2047
public import Certificates.Data.Kernel.SporSch.Co1Stab
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.Co1B
public import Certificates.Data.Kernel.Co1BW
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.H24512

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.EvenSporadicStandard.TwoCo1.HypOne
  CFSG.Sporadic.Co1Block
open CFSG.KC.Co1B (mulWK)

theorem kPb : allN twoCBray.length (fun i => Nat.beq (PC.M i) (C2047.D2.M i)) = true := by
  quickRfl
theorem kP : dagIK PC.M PC.MI twoCBray.length PC.N perfPC = true := by quickRfl
theorem kpi : perfPIdxC.all (fun j => decide (j < PC.N)) = true := by quickRfl
theorem kUb : allN perfPIdxC.length (fun l => Nat.beq (UC.M l) (PC.M (perfPIdxC.getD l 0))) =
    true := by quickRfl
theorem kU : dagIK UC.M UC.MI perfPIdxC.length UC.N perfUC = true := by quickRfl
theorem kci : perfCIdxC.all (fun ij => decide (ij.1 < UC.N) && decide (ij.2 < UC.N)) = true := by
  quickRfl
theorem kFb : allN perfCIdxC.length (fun j => Nat.beq (FC.M j)
    (mulWK (mulWK (UC.MI (perfCIdxC.getD j (0, 0)).1) (UC.MI (perfCIdxC.getD j (0, 0)).2))
      (mulWK (UC.M (perfCIdxC.getD j (0, 0)).1) (UC.M (perfCIdxC.getD j (0, 0)).2)))) = true := by
  quickRfl
theorem kF : dagIK FC.M FC.MI perfCIdxC.length FC.N perfFC = true := by quickRfl
theorem kfi : perfFIdxC.all (fun j => decide (j < FC.N)) = true := by quickRfl
theorem kf : allN perfPIdxC.length
    (fun l => Nat.beq (FC.M (perfFIdxC.getD l 0)) (PC.M (perfPIdxC.getD l 0))) = true := by
  quickRfl
theorem kQb : allN perfPIdxC.length (fun l => Nat.beq (QC.M l) (PC.M (perfPIdxC.getD l 0))) =
    true := by quickRfl
theorem kQ : dagIK QC.M QC.MI perfPIdxC.length QC.N perfQC = true := by quickRfl
theorem kqi : perfQIdxC.all (fun j => decide (j < QC.N)) = true := by quickRfl
theorem kq : allN perfQIdxC.length (fun l => Nat.beq (QC.M (perfQIdxC.getD l 0))
    (C2047.D2.M (twoCQGens.getD l 0))) = true := by quickRfl

end CertificateChecks.KernelCo1B.H24512

end
