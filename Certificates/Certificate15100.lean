module

public import CFSG.Sporadic.SuzRecog.RigidL2Tests
import Certificates.Kernel.Sporadic.OddCore.SuzRg

public section

open CFSG

namespace Certificates

open CertificateChecks

theorem certificate15100 : CFSG.Sporadic.SuzRecog.RigidL2.rigLiftOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigUCompleteOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigGenOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigCommOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigDecompOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigCenterOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigStabOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigX1OK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigX2OK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigBfsOK = true ∧
    CFSG.Sporadic.SuzRecog.RigidL2.rigIrredOK = true :=
  KernelSpor.SuzRg.checks

end Certificates
