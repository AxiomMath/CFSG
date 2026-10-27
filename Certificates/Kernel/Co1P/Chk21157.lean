module

public import Certificates.Kernel.Co1P.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1P CFSG.KC.Co1F2 CFSG.KD.Co1P CFSG.KLie.CT
  CFSG.Sporadic.Co1Patterson.Native

@[expose] noncomputable def wK (i : Nat) : Nat :=
  mulWK (mulWK (mulWK (hsW orbQMasks i) (repXK 0)) AL) (mulWK (repXiK 0) (hisW orbQMasks i))

@[expose] noncomputable def ptE (k : Nat) : Nat :=
  mulWK (mulWK (hsW orbEMasks k) (repK 1)) (hisW orbEMasks k)

@[expose] noncomputable def amalK : Bool :=
  andB (eqK (ptE 3940) (mulWK AL (repK 1)))
    (eqK (mulWK (mulWK (getL oneK GDS 94) (wK 64)) (getL oneK GDIS 94)) (wK 128))

theorem amal_chk : amalK = true := by quickRfl

theorem amal_neg : notB (eqK (ptE 3941) (mulWK AL (repK 1))) = true := by quickRfl

end CertificateChecks.KernelCo1P

end
