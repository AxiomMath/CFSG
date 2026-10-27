module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B9c
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7008 : ∀ e ∈ batch9_3, Elim.Hs e.k e.lam e.neg ≠ 0 := by
  intro e he
  simp only [batch9_3, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [B93.E0.ok, B93.E1.ok, B93.E2.ok, B93.E3.ok, B93.E4.ok, B93.E5.ok, B93.E6.ok,
    B93.E7.ok, B93.E8.ok, B93.E9.ok]

end Certificates
