module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B9e
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7010 : ∀ e ∈ batch9_5, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  intro e he
  simp only [batch9_5, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [B95.E0.ok, B95.E1.ok, B95.E2.ok, B95.E3.ok, B95.E4.ok, B95.E5.ok, B95.E6.ok,
    B95.E7.ok, B95.E8.ok]

end Certificates
