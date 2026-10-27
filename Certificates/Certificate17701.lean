module

public import CFSG.HardMathSupport.Dickson.BMRows.M11SylowInputs
import Certificates.Kernel.KDenseP.MW17701

public section

namespace Certificates

open CertificateChecks

theorem certificate17701 :
    CFSG.HardMathSupport.Dickson.BMRows.M11.m11Check () = true :=
  KernelKDenseP.MW.c17701

end Certificates
