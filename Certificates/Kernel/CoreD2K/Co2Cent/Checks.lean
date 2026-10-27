module

public import Certificates.Kernel.CoreD2K.Co2Cent.Data
public import Certificates.Kernel.CoreD2K.Co2Cent.Datum
public import Certificates.Kernel.CoreD2K.Co2.Data
public import Certificates.Data.Kernel.CoreD2K.Steps
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.Co2Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.Co2 (GP GPI)

theorem k_g : allN co2CentK.base.gWs.length (fun j => bAnd(wordEqK 2300 12 (mask 12)
    (pidn 2300 12) GP GPI (nat_lit 2) (co2CentK.base.gWs.getD j []) (GT j),
    permOK 2300 12 (mask 12) (Nat.mul 2300 12) (GT j) (GTI j))) = true := by quickRfl
theorem k_kinds : kindsK 2300 12 co2CentK Co2.RE.G GT = true := by quickRfl
theorem k_rep4 : repCK 2300 12 co2CentK GP GT GTI 4 = true := by quickRfl
theorem k_steps : co2CentSteps.all (stepCK 2300 12 co2CentK Co2.RE.G GT) = true := by quickRfl
theorem k_chain : chainOK co2CentK.ys.length co2CentReps co2CentSteps = true := by quickRfl

end CertificateChecks.KernelCoreD2K.Co2Cent

end
