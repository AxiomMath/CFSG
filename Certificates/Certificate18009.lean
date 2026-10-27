module

public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterCheck
import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Sporadic.Schreier.LyCheckSeven

public section

namespace Certificates

open CertificateChecks

theorem certificate18009 : (
    CFSG.Sporadic.LySchreier.Native.bsCertificate () = true
  ) := KernelSporSch.LyBSF.facts

end Certificates
