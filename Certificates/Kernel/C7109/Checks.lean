module

public import Certificates.Data.Kernel.C7109.Check
public import Certificates.Kernel.C7109.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelC7109

open CFSG.KC.C7109 CFSG.KD.C7109

set_option maxRecDepth 100000 in
theorem c7109_recs : recsOK MT RL = true := by quickRfl

set_option maxRecDepth 100000 in
theorem c7109_compl : complOK MT = true := by quickRfl

set_option maxRecDepth 100000 in
theorem c7109_walk :
    letB singMask (fun S => walkP S 7 0 0 List.nil 4294967295 4294967295 List.nil RL) = true := by
  quickRfl

end CertificateChecks.KernelC7109

end
