module

public import Certificates.Data.TabMThreeALeech
public meta import Certificates.Data.TabMThreeALeech
public import Certificates.Kernel.Co1B.Chk17597
public import Certificates.Kernel.Co1B.C17590
public import Certificates.Kernel.Co1ThreeK.LettersEq
public import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CertificateChecks.KernelCo1B.Fix17597

open CFSG.KC.Co1F2 CFSG.KC.Co1B CertificateChecks.KernelCo1M
  CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

theorem mul_unpackWK (A B : Nat) :
    CFSG.Sporadic.Co1Schreier.Native.mul (unpackR 24 A) (unpackR 24 B) = unpackR 24 (mulWK A B) :=
  CFSG.KC.F2W.mul_unpackW A B

theorem m_eq {X Y : Nat} (h : Nat.beq X Y = true) : unpackR 24 X = unpackR 24 Y := by
  rw [Nat.eq_of_beq_eq_true h]

theorem c0_eq : c0Rows () = unpackR 24 D0.M := by
  have h27 := c71_rr (i := 27) (by rw [c71_len]; norm_num)
  have h70 := c71_rr (i := 70) (by rw [c71_len]; norm_num)
  rw [c0Rows, h27, h70, mul_unpackWK]
  exact m_eq m0_chk

theorem root0_eq : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 0 =
    unpackR 24 D1.M := by
  rw [CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide),
    ← CFSG.KS.SporSch.M24.unpackR_eq_unpack]
  exact m_eq m1_chk

theorem root2_eq : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 2 =
    unpackR 24 D2.M := by
  rw [CertificateChecks.KernelCo1ThreeK.rootRows_eq (by decide),
    ← CFSG.KS.SporSch.M24.unpackR_eq_unpack]
  exact m_eq m2_chk

theorem threeA_eq : threeARows () = unpackR 24 D3.M := by
  rw [threeARows, CertificateChecks.KernelSporSch.Co1Elem.aRows_eq]
  simp only [← CFSG.KS.SporSch.M24.unpackR_eq_unpack]
  rw [mul_unpackWK, mul_unpackWK]
  exact m_eq m3_chk

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech in
theorem c17597 : threeAFix () = [4096, 64, 256, 1] := by
  rw [threeAFix, c0_eq, root0_eq, root2_eq, threeA_eq, CFSG.KC.F2W.transposeRows_unpackR,
    CFSG.KC.F2W.transposeRows_unpackR, CFSG.KC.F2W.transposeRows_unpackR,
    CFSG.KC.F2W.transposeRows_unpackR, Fix17590.fixCount_one, Fix17590.fixCount_one,
    Fix17590.fixCount_one, Fix17590.fixCount_one, (CFSG.KC.Co1Fix.fixK_sound fix0_chk).1,
    (CFSG.KC.Co1Fix.fixK_sound fix1_chk).1, (CFSG.KC.Co1Fix.fixK_sound fix2_chk).1,
    (CFSG.KC.Co1Fix.fixK_sound fix3_chk).1]

end CertificateChecks.KernelCo1B.Fix17597

end
