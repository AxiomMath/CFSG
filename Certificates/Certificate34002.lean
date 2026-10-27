module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenU35Inputs
import Certificates.Kernel.ExactGen.U35

public section

namespace Certificates

open CertificateChecks

theorem certificate34002 : CFSG.ComponentClassification.SolMax.SwapP2.ExactFin.u35FCCheck () = true := KernelEG.U35.check

end Certificates
