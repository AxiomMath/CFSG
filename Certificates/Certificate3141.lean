module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23LeviInputs
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
import Certificates.Kernel.TwoE6.Levi

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.TwoE6 Matrix CFSG.Monster.B.Classical.UnitarySix
    CFSG.LieType.Universal.Unitary in
theorem certificate3141 : (outA.det = 1)
    ∧ ((outA.map bar)ᵀ * CFSG.LieType.Universal.Unitary.antidiag 6 * outA = CFSG.LieType.Universal.Unitary.antidiag 6)
    ∧ (outN.det = 1)
    ∧ ((outN.map bar)ᵀ * CFSG.LieType.Universal.Unitary.antidiag 6 * outN = CFSG.LieType.Universal.Unitary.antidiag 6)
    ∧ (outA * betaM outA = 1)
    ∧ (outN * outA * betaM outN = outA)
    ∧ (outN * outN = outNPow 0)
    ∧ (outNPow 0 * outNPow 0 = outNPow 1)
    ∧ (outNPow 1 * outNPow 1 = outNPow 2)
    ∧ (outNPow 2 * outNPow 0 * outN = 1) := KernelTwoE6.cert3141

end Certificates
