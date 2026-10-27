module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs
import Certificates.Kernel.Co2Three.UqGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T in
theorem certificate101704 : ∀ A : Subgroup (Equiv.Perm (Fin 2300)), A ≤ Qg → CFSG.Open.IsElemAbelian 3 A →
    Nat.card A = 3 ^ 4 → A ≤ Subgroup.closure {x | ∃ k < 81, dEltP k = x} :=
  fun A hAQ hA hc => KernelCo2Three.kuniq A hAQ (fun x hx y hy => by
      have := hA.1
      exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩))
    hA.2 (by rw [hc]; norm_num)

end Certificates
