module

public import CFSG.Sporadic.HNOddCore.InvDefs
public import CFSG.Sporadic.HNOddCore.RAction
import Certificates.Kernel.HNClsL.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore in
theorem certificate14963 :     ∃ (Q : Subgroup JH) (xs : ℕ → JH),
      (∀ q ∈ Q, jR q * jR aJ = jR aJ * jR q) ∧ Nat.card Q = 125 ∧
      (∀ z ∈ Q, orderOf z = 5 → ∃ i < 7, ∃ g : JH, jR g * jR aJ = jR aJ * jR g ∧
          Subgroup.zpowers z = Subgroup.zpowers (g * xs i * g⁻¹)) ∧
      (∀ i < 7, ∃ l : List JH, (∀ k ∈ l, k * xs i = xs i * k) ∧
          5 ∣ orderOf ((l.map fun k => MulAut.conj k * conjR (jR aJ) * (MulAut.conj k)⁻¹).prod)) := by
  intros
  exact KernelHNClsL.factsA

end Certificates
