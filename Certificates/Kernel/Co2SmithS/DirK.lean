module

public import Certificates.Kernel.Co2SmithS.Lets
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def seedsK : Array (Array Nat) :=
  #[CFSG.KC.Co1F2.unpackR 22 (LT 0), CFSG.KC.Co1F2.unpackR 22 (LT 1)]

theorem beta_k : betaOK seedsK = true := by decide +kernel

theorem frame_k : frameOK seedsK = true := by decide +kernel

theorem zeta_k : zetaOK seedsK = true := by decide +kernel

theorem res_k : resOK seedsK = true := by decide +kernel

end CertificateChecks.KernelCo2SmithS

end
