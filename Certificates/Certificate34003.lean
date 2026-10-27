module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenPSp45Inputs
import Certificates.Kernel.ExactGen.PSp45

public section

namespace Certificates

open CertificateChecks

theorem certificate34003 : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.psp45FCCheck () = true := KernelEG.PSp45.check

end Certificates
