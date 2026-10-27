
module

public import Certificates.Kernel.Co1M.W10070
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam
  CFSG.KC.Co1B CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

theorem inv_k1 : stepsK (w70.reg 2) 0 (w70.reg 2) (w70.reg 2) = true := by quickRfl

theorem inv_k2 : stepsK (w70.reg 3) 1 (w70.reg 3) (w70.reg 12) = true := by quickRfl

theorem inv_n1 : stepsK (w70.reg 4) 0 (w70.reg 4) (w70.reg 4) = true := by quickRfl

theorem inv_n2 : stepsK (w70.reg 5) 4 (w70.reg 5) (w70.reg 13) = true := by quickRfl

theorem rep_A_chk : andB (Nat.beq (mulF 24 (w70.reg 2) (w70.reg 2)) (idF 24))
    (andB (Nat.beq (mulF 24 (w70.reg 3) (w70.reg 12)) (idF 24))
    (andB (orderIsK 24 (w70.reg 7) 2) (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 7)) code3) code3)
    (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 2)) code3) code3)
      (Nat.beq (vmF 24 (trK 24 (w70.reg 3)) code3) code3))))) = true := by quickRfl

theorem rep_B_chk : andB (Nat.beq (mulF 24 (w70.reg 4) (w70.reg 4)) (idF 24))
    (andB (Nat.beq (mulF 24 (w70.reg 5) (w70.reg 13)) (idF 24))
    (andB (orderIsK 24 (w70.reg 9) 2) (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 9)) code4) code4)
    (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 4)) code4) code4)
      (Nat.beq (vmF 24 (trK 24 (w70.reg 5)) code4) code4))))) = true := by quickRfl

theorem rep_C_chk : andB (Nat.beq (mulF 24 (w70.reg 4) (w70.reg 4)) (idF 24))
    (andB (Nat.beq (mulF 24 (w70.reg 5) (w70.reg 13)) (idF 24))
    (andB (orderIsK 24 (w70.reg 11) 2) (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 11)) code4) code4)
    (andB (Nat.beq (vmF 24 (trK 24 (w70.reg 4)) code4) code4)
      (Nat.beq (vmF 24 (trK 24 (w70.reg 5)) code4) code4))))) = true := by quickRfl

theorem qt_chk : Nat.beq (trK 24 CertificateChecks.KernelCo1Cover.QP) Qt70 = true := by quickRfl

theorem wit_A_chk : andB (stepsK (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 [false, false, false, false] oneK) 1
    (wordABFrom CertificateChecks.KernelCo1Cover.R0 CertificateChecks.KernelCo1Cover.R1
      [false, false, false, false] oneK) (w70.reg 1 |> fun B => mulF 24 B B))
    (andB (Nat.beq (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [false, false, false, false] oneK)
      (w70.reg 1 |> fun B => mulF 24 B B)) (idF 24))
    (orderIsK 24 (mulF 24 (mulF 24 (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [false, false, false, false] oneK) (w70.reg 7))
      (w70.reg 1 |> fun B => mulF 24 B B)) (w70.reg 7)) 3)) = true := by quickRfl

theorem wit_B_chk : andB (stepsK (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 [false] oneK) 1
    (wordABFrom CertificateChecks.KernelCo1Cover.R0 CertificateChecks.KernelCo1Cover.R1
      [false] oneK) (w70.reg 1 |> fun B => mulF 24 B B))
    (andB (Nat.beq (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [false] oneK)
      (w70.reg 1 |> fun B => mulF 24 B B)) (idF 24))
    (orderIsK 24 (mulF 24 (mulF 24 (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [false] oneK) (w70.reg 7))
      (w70.reg 1 |> fun B => mulF 24 B B)) (w70.reg 9)) 10)) = true := by quickRfl

theorem wit_C_chk : andB (stepsK (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK) 38
    (wordABFrom CertificateChecks.KernelCo1Cover.R0 CertificateChecks.KernelCo1Cover.R1
      [true, true, true, false] oneK) (powK 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK) 39))
    (andB (Nat.beq (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK)
      (powK 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
        CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK) 39)) (idF 24))
    (orderIsK 24 (mulF 24 (mulF 24 (mulF 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
      CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK) (w70.reg 7))
      (powK 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
        CertificateChecks.KernelCo1Cover.R1 [true, true, true, false] oneK) 39)) (w70.reg 11))
      12)) = true := by quickRfl

theorem q0_code3_chk : dotN code3 (vmF 24 Qt70 code3) = true := by quickRfl

theorem q0_code4_chk : notB (dotN code4 (vmF 24 Qt70 code4)) = true := by quickRfl

theorem code4_chk : Nat.beq (vmF 24 (trK 24 (wordABFrom CertificateChecks.KernelCo1Cover.R0
    CertificateChecks.KernelCo1Cover.R1 code4Word oneK)) 1) code4 = true := by quickRfl

theorem qs_chk : (OFF70.all fun o => Nat.beq (qCountK 24 Qt70 FAt70 o) 1920) = true := by
  quickRfl

theorem fixA_fix :
    (FA70.all fun f => Nat.blt f (2 ^ 24) && Nat.beq (vmF 24 (w70.regT 7) f) f) = true := by
  quickRfl

theorem fixA_pivF : pivK 24 FA70 0 = true := by quickRfl

theorem fixA_pivY : pivK 24 (YA70.map fun y => Nat.xor (vmF 24 (w70.regT 7) y) y) 0 = true := by
  quickRfl

theorem fix_B : fixK 24 (w70.regT 9) Qt70 FB70 YB70 12 4096 0 = true := by quickRfl

theorem fix_C : fixK 24 (w70.regT 11) Qt70 FC70 YC70 12 4096 2048 = true := by quickRfl

end CertificateChecks.KernelCo1M

end
