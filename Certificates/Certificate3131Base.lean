
module

public import CFSG.Monster.B.GSide.MuFourOmegaInputs
public import Certificates.Kernel.MonsterB.Co2Mem
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.B.GSide.MuFourGeneric
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import CFSG.Monster.B.TwoA.Unitary.Bridge
public import CFSG.Monster.B.TwoA.Unitary.ActionInputs

@[expose] public section

open CFSG.Monster.B CFSG.Monster.B.GSide CFSG.KC.Co2Mem CFSG.KLie.CT CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3131

set_option maxRecDepth 100000

theorem k2652785 : memK 2300 24 (Co2V.F 0) 2652785 = true := by quickRfl

theorem bW_q₁_q₂ : bWcode 24606 2652785 ≠ 0 := by decide +kernel

end CertificateChecks.Batch3131

namespace Certificates

end Certificates
