module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
import Certificates.Kernel.FourJ2J3.J2Final
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace Certificates

open CertificateChecks

theorem certificate320201 : CFSG.ComponentClassification.Sol76.Sig.GSYard02.SylowFourJoined
    ↥CFSG.Sporadic.Schreier.j2P :=
  KernelFourJ2J3.sylowFourJoined_j2P_kernel

end Certificates
