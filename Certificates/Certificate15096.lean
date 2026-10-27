module

public import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests
import Certificates.Kernel.Sporadic.OddCore.SuzRFF

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15096 : CFSG.Sporadic.SuzRecog.LocalR.sizesCheck = true ∧
    CFSG.Sporadic.SuzRecog.LocalR.genCheck = true ∧
    CFSG.Sporadic.SuzRecog.LocalR.orbits2Check = true ∧
    CFSG.Sporadic.SuzRecog.LocalR.sylow2Check = true ∧
    CFSG.Sporadic.SuzRecog.LocalR.v02Check = true ∧
    CFSG.Sporadic.SuzRecog.LocalR.repsCheck = true :=
  ⟨KernelSpor.SuzRF.sizes_true, KernelSpor.SuzRF.gen_true, KernelSpor.SuzRF.orbits_true,
    KernelSpor.SuzRF.sylow_true, KernelSpor.SuzRF.v0_true, KernelSpor.SuzRF.reps_true⟩

end Certificates
