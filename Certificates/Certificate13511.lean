module

public import Certificates.Data.B3Spor3.M11
public import Certificates.Data.B3Spor3.M12
public import Certificates.Data.B3Spor3.M22
public import Certificates.Data.B3Spor3.M23
public meta import Certificates.Data.B3Spor3.M11
public meta import Certificates.Data.B3Spor3.M12
public meta import Certificates.Data.B3Spor3.M22
public meta import Certificates.Data.B3Spor3.M23
import Certificates.Kernel.B3S3.M11Facts
import Certificates.Kernel.B3S3.M12Facts
import Certificates.Kernel.B3S3.M22Facts
import Certificates.Kernel.B3S3.M23Facts
import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem certificate13511 : check m11S3Data = true ∧ check m12S3Data = true ∧ check m22S3Data = true ∧
    check m23S3Data = true :=
  ⟨KernelB3S3.M11.m11_ok, KernelB3S3.M12.m12_ok, KernelB3S3.M22.m22_ok, KernelB3S3.M23.m23_ok⟩

end Certificates
