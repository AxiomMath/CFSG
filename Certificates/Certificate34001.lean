module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenJ2Inputs
import Certificates.Kernel.ExactGen.J2

public section

namespace Certificates

open CertificateChecks

theorem certificate34001 : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.j2FCCheck () = true := KernelEG.J2.check

end Certificates
