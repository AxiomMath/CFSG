module

public import CFSG.Sporadic.SuzRecog.B0GluingTests
import Certificates.Kernel.Sporadic.OddCore.SuzGl

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate15110 : CFSG.Sporadic.SuzRecog.B0Gluing.idxCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.thetaCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.autCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.planeCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.centRCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.tauZCheck = true ∧
    CFSG.Sporadic.SuzRecog.B0Gluing.rhoACheck = true :=
  ⟨SuzGl.idxCheck_true, SuzGl.thetaCheck_true, SuzGl.autCheck_true, SuzGl.planeCheck_true,
    SuzGl.centRCheck_true, SuzGl.tauZCheck_true, SuzGl.rhoACheck_true⟩

end Certificates
