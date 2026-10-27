module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B9a
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7006 : ∀ e ∈ batch9_1, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  intro e he
  simp only [batch9_1, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [B91.E0.ok, B91.E1.ok, B91.E2.ok, B91.E3.ok, B91.E4.ok, B91.E5.ok, B91.E6.ok,
    B91.E7.ok, B91.E8.ok, B91.E9.ok]

end Certificates
