module

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.RAction
import Certificates.Kernel.HNClsL.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore in
theorem certificate14965 :     ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * t1R = t1R * jR q) ∧ Nat.card Q = 25 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 3, ∃ g : JH, jR g * t1R = t1R * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 3, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR t1R * (MulAut.conj k)⁻¹).prod)) := by
  intros
  exact KernelHNClsL.factsC

end Certificates
