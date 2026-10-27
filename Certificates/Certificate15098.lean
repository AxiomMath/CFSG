module

public import CFSG.Sporadic.SuzRecog.C1ModelTests
import Certificates.Kernel.Sporadic.OddCore.SuzC1BF
import Certificates.Kernel.Sporadic.OddCore.SuzC1EF
import Certificates.Kernel.Sporadic.OddCore.SuzC1EV
import Certificates.Kernel.Sporadic.OddCore.SuzC1EZ
import Certificates.Kernel.Sporadic.OddCore.SuzC1EL

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15098 : CFSG.Sporadic.SuzRecog.C1Model.baseCheck = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.resCheck = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.t0Check = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.v0Check = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.centCheck = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.locCheck = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.rhoCheck = true ∧
    CFSG.Sporadic.SuzRecog.C1Model.normCheck = true :=
  ⟨SuzC1BF.baseCheck_true, SuzC1BF.resCheck_true, SuzC1EF.t0Check_true, SuzC1EV.v0Check_true,
    SuzC1EZ.centCheck_true, SuzC1EL.locCheck_true, SuzC1EL.rhoCheck_true,
    SuzC1EF.normCheck_true⟩

end Certificates
