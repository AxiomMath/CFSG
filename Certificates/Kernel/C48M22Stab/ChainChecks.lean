module

public import Certificates.Kernel.C48M22Stab.ChainData
public import Certificates.Kernel.KGC31M22.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC48M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSporSch CertificateChecks.KernelKGC31M22

theorem kA0 : abOK (eW 0) = true := by quickRfl
theorem kA1 : abOK (eW 1) = true := by quickRfl

theorem kW0 : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1)
    (M22Q.SI 1) (eW 0)) (CE8.S 0) = true := by quickRfl
theorem kW1 : Nat.beq (abWordK 22 5 (mask 5) (pidn 22 5) (M22Q.S 0) (M22Q.SI 0) (M22Q.S 1)
    (M22Q.SI 1) (eW 1)) (CE8.S 1) = true := by quickRfl

theorem kP0 : permOK 22 5 (mask 5) (22 * 5) (CE8.S 0) (CE8.SI 0) = true := by quickRfl
theorem kP1 : permOK 22 5 (mask 5) (22 * 5) (CE8.S 1) (CE8.SI 1) = true := by quickRfl

theorem kOrd : Nat.beq (ordK CE8.LR 3) 1344 = true := by quickRfl

theorem kM0 : pmasksOK 22 5 e8P (CE8.S 0) [1, 4, 2] = true := by quickRfl
theorem kM1 : pmasksOK 22 5 e8P (CE8.S 1) [5, 3, 7] = true := by quickRfl

end CertificateChecks.KernelC48M22

end
