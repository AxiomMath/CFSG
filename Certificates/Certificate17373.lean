module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBMCover
import Certificates.Kernel.Fi22RkInv.Glue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase

public section

namespace Certificates

open CertificateChecks

theorem certificate17373 : ∀ k < 4,
    CFSG.HardMathSupport.Dickson.I271.RkBMInvAt
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three.xRep k) :=
  fun _ hk => KernelFi22RkInv.rkBMInvAt_xRep hk

end Certificates
