module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.CU43Aut.SylData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def swOK (g j j' : Nat) : Bool :=
  bAnd(inPK g, Nat.beq (pc (pc g (CU43T 0)) (CU43T (Nat.add j 2)))
    (pc (CU43T (Nat.add j' 2)) (pc g (CU43T 0))))

theorem kSwap : bAnd(swOK (SWP 0) 0 1, bAnd(swOK (SWP 1) 4 5, swOK (SWP 2) 7 6)) = true := by
  quickRfl

end CertificateChecks.KernelCU43Aut

end
