module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
import Certificates.Kernel.FourJ2J3.J3Final
public import CFSG.Sporadic.Schreier.PairJ3CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate320202 : CFSG.ComponentClassification.Sol76.Sig.GSYard02.SylowFourJoined
    ↥CFSG.Sporadic.Schreier.j3P :=
  KernelFourJ2J3.sylowFourJoined_j3P_kernel

end Certificates
