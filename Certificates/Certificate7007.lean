module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B9b
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7007 : ∀ e ∈ batch9_2, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  intro e he
  simp only [batch9_2, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [B92.E0.ok, B92.E1.ok, B92.E2.ok, B92.E3.ok, B92.E4.ok, B92.E5.ok, B92.E6.ok,
    B92.E7.ok, B92.E8.ok, B92.E9.ok]

end Certificates
