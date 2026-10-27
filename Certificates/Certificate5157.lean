module

public import Certificates.Data.GH74IvkCentJ2
public meta import Certificates.Data.GH74IvkCentJ2
import Certificates.Kernel.GH74.J2Norm
import Certificates.Kernel.GH74.J2Ev
import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate2233
import Certificates.Certificate2234
import Certificates.Certificate2278

public section

namespace Certificates

open CertificateChecks

theorem certificate5157 : IvkCent.j2CentInnerCount = 12 ∧ IvkCent.j2CentOuterCount = 0 :=
  ⟨KernelGH74.J2Norm.innerCount_eq, KernelGH74.J2Norm.outerCount_eq⟩

end Certificates
