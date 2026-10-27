module

public import Certificates.Data.Kernel.AE6Tri.DefsTA
public import Certificates.Kernel.AE6Tri.DataTA
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6TriTA

open CFSG.KC.Enum CFSG.KC.AE6Tri CFSG.KD.AE6TA

theorem kTaQ8 : strictB (nthN taLL (nthN taKI 0)) (fun I => strictB (nthN taLL (nthN taKI 1))
    (fun I' => strictB (nthN taLL (nthN taKI 2)) (fun J => allN 360 (fun x =>
      bAnd(Nat.beq (ap I (ap I x)) (ap J (ap J x)), Nat.beq (ap I (ap J x)) (ap J (ap I' x))))))) =
    true := by quickRfl

end CertificateChecks.KernelAE6TriTA

end
