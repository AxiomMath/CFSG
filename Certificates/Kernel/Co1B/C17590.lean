module

public import Certificates.Data.TabCo1ThreeD
public meta import Certificates.Data.TabCo1ThreeD
public import Certificates.Kernel.Co1B.Chk17590
public import Certificates.Kernel.Co1M.C10071
public import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CertificateChecks.KernelCo1B.Fix17590

open CFSG.KC.Co1F2 CertificateChecks.KernelCo1M CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD

theorem countBelow_eq (p q : Nat → Bool) (h : ∀ x, p x = q x) : ∀ n acc,
    CFSG.Sporadic.Co1.OddNative.countBelow p n acc = CFSG.Sporadic.Co1.InvNative.countBelow q n acc
  | 0, _ => rfl
  | n + 1, acc => by
    rw [CFSG.Sporadic.Co1.OddNative.countBelow, CFSG.Sporadic.Co1.InvNative.countBelow, h n]
    exact countBelow_eq p q h n _

theorem fixCount_one (Mt : Array Nat) :
    CFSG.Sporadic.Co1.OddNative.fixCount [Mt] = CFSG.Sporadic.Co1.InvNative.fixCount Mt := by
  rw [CFSG.Sporadic.Co1.OddNative.fixCount, CFSG.Sporadic.Co1.InvNative.fixCount]
  refine countBelow_eq _ _ (fun x => ?_) _ _
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rfl

theorem c1_eq : c1Rows () = unpackR 24 C1K := by
  have h27 := c71_rr (i := 27) (by rw [c71_len]; norm_num)
  have h73 := c71_rr (i := 73) (by rw [c71_len]; norm_num)
  rw [c1Rows, h27, h73, CFSG.KC.F2W.mul_unpackW]
  rfl

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD in
theorem c17590 : threeDFix () = 256 := by
  rw [threeDFix, c1_eq, CFSG.KC.F2W.transposeRows_unpackR, fixCount_one]
  exact (CFSG.KC.Co1Fix.fixK_sound fix_chk).1

end CertificateChecks.KernelCo1B.Fix17590

end
