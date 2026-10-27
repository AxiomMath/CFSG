
module

public import Certificates.Certificate2059Base

public import CFSG.Sporadic.Co2Schreier.SylowCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Kernel.SporSch.Co2M.FratPG
import Certificates.Kernel.SporSch.Co2M.Neg2059
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.Co2Schreier

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier in
theorem certificate2059 : (fratCheck fratLevels = true)
    ∧ (profileOK fratLevels zArr profTable = true)
    ∧ (uniqueOK profTable = true) :=
  ⟨KernelSporSch.Co2M.frat_check, KernelSporSch.Co2M.profile_check, unique_check⟩

end Certificates
