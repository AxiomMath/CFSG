module

public import CFSG.Sporadic.Recognition.McLASInputs
public import CFSG.Sporadic.Recognition.McLASThreeFacts
import Certificates.Kernel.McLAS.SixF
import Certificates.Certificate2240
import Certificates.Certificate2241

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS in
theorem certificate6105 : (m11Check = true) ∧ (invProdCheck = true) ∧ ThreeFacts ∧ (fiveOuterCheck = true) ∧
    (fivePowerCheck = true) ∧ (sylowThreeOK = true) :=
  ⟨KernelMcLAS.m11_ok, KernelMcLAS.invProd_ok, KernelMcLAS.threeFacts, KernelMcLAS.fiveOuter_ok,
    KernelMcLAS.fivePower_ok, KernelMcLAS.sylowThree_ok⟩

end Certificates
