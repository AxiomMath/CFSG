module

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.RAction
import Certificates.Kernel.HNClsL.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore in
theorem certificate14964 :     ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * jR CFSG.Sporadic.HNOddCore.t4J = jR CFSG.Sporadic.HNOddCore.t4J * jR q) ∧ Nat.card Q = 25 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 5, ∃ g : JH, jR g * jR CFSG.Sporadic.HNOddCore.t4J = jR CFSG.Sporadic.HNOddCore.t4J * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 5, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR (jR CFSG.Sporadic.HNOddCore.t4J) * (MulAut.conj k)⁻¹).prod)) := by
  intros
  exact KernelHNClsL.factsB

end Certificates
