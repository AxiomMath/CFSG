module

public import Certificates.Data.GrSLitL34FactsFourCubeWit
import Certificates.Kernel.HS100.CubeFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts.FourCube in
theorem certificate22218 : fourCubeWitOK = true := KernelHS100.fourCube

end Certificates
