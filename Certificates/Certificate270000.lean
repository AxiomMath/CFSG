module

public import CFSG.ClassicalInvolution.Q3.Q3SJ2Inputs
public import CFSG.ClassicalInvolution.Q3.Q3SJ3Inputs
import Certificates.Kernel.Q3Wit.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate270000 : CFSG.ClassicalInvolution.Q3.j2WitnessCheck = true ∧
    CFSG.ClassicalInvolution.Q3.j3WitnessCheck = true :=
  ⟨KernelQ3Wit.j2_check, KernelQ3Wit.j3_check⟩

end Certificates
