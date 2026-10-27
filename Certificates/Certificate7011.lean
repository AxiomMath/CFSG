module

public import CFSG.Walter.Ree.Bombieri.Stage2Data
import Certificates.Kernel.Misc.Ree2.B87
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace Certificates

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec CertificateChecks.KernelRee2

open CFSG.Walter.Ree.Bombieri CFSG.Walter.Ree.Bombieri.Spec in
theorem certificate7011 : (∀ e ∈ batch8, Elim.Hs e.k e.lam e.neg ≠ 0) ∧ (∀ e ∈ batch7, Elim.Hs e.k e.lam e.neg ≠ 0) := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · simp only [batch8, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    exacts [B8.E0.ok, B8.E1.ok, B8.E2.ok, B8.E3.ok]
  · simp only [batch7, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    exacts [B7.E0.ok, B7.E1.ok]

end Certificates
