module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B9d
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7009 : ∀ e ∈ batch9_4, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  intro e he
  simp only [batch9_4, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [B94.E0.ok, B94.E1.ok, B94.E2.ok, B94.E3.ok, B94.E4.ok, B94.E5.ok, B94.E6.ok,
    B94.E7.ok, B94.E8.ok, B94.E9.ok]

end Certificates
