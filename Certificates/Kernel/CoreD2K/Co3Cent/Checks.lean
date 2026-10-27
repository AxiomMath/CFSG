module

public import Certificates.Kernel.CoreD2K.Co3Cent.Data
public import Certificates.Kernel.CoreD2K.Co3Cent.Datum
public import Certificates.Kernel.CoreD2K.Co3.Data
public import Certificates.Data.Kernel.CoreD2K.Steps
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 10

namespace CertificateChecks.KernelCoreD2K.Co3Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CoreD2K
open Certificates.CoreD2Perm
open CertificateChecks.KernelCoreD2K.Co3 (GP GPI)

theorem k_g : allN co3CentK.base.gWs.length (fun j => bAnd(wordEqK 276 9 (mask 9) (pidn 276 9) GP
    GPI (nat_lit 2) (co3CentK.base.gWs.getD j []) (GT j),
    permOK 276 9 (mask 9) (Nat.mul 276 9) (GT j) (GTI j))) = true := by quickRfl
theorem k_kinds : kindsK 276 9 co3CentK Co3.RE.G GT = true := by quickRfl
theorem k_rep1 : repCK 276 9 co3CentK GP GT GTI 1 = true := by quickRfl
theorem k_rep3 : repCK 276 9 co3CentK GP GT GTI 3 = true := by quickRfl
theorem k_steps : co3CentSteps.all (stepCK 276 9 co3CentK Co3.RE.G GT) = true := by quickRfl
theorem k_chain : chainOK co3CentK.ys.length co3CentReps co3CentSteps = true := by quickRfl

end CertificateChecks.KernelCoreD2K.Co3Cent

end
