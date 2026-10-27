module

public import Certificates.Kernel.Co2Census.S0Data

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census

@[expose] def trOff (k : Nat) : Nat := [0, 63, 95, 110, 118, 121].getD k 0

@[expose] noncomputable def SK (n : Nat) : Nat :=
  mulV (TRt (n % 63)) (mulV (TRt (63 + n / 63 % 32)) (mulV (TRt (95 + n / 2016 % 15))
    (mulV (TRt (110 + n / 30240 % 8)) (mulV (TRt (118 + n / 241920 % 3))
      (TRt (121 + n / 725760 % 2))))))

@[expose] noncomputable def stL : Nat → Nat → Nat := conjStep ABt ABIt

end CertificateChecks.KernelCo2Census

end
