
module

public import CFSG.RankThree.Native.ONTripleAutSpInputs
import Certificates.Kernel.ON8138.Glue
import Certificates.Kernel.ON8138.A6Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple Equiv in
theorem certificate8138 : (r0Check = true)
    ∧ (spCheckA = true)
    ∧ (
 ∀ u₁ u₂ : Perm (Fin 6), u₁ ^ 3 = 1 → u₂ ^ 3 = 1 → (u₁ * u₂) ^ 5 = 1 →
    evW u₁ u₂ Wy0 = sY 0 → evW u₁ u₂ Wy1 = sY 1 → evW u₁ u₂ Wt4 = s4 →
      u₁ = sK1 ∧ u₂ = sK2
)
    ∧ (
 ∀ t : Perm (Fin 6), t * sY 0 = sY 0 * t → t * sY 1 = sY 1 * t →
    ∃ a < 3, ∃ b < 3, t = sY 0 ^ a * sY 1 ^ b
) :=
  ⟨KernelON8138.r0Check_true, KernelON8138.spCheckA_true, KernelON8138.a6_rigid',
    KernelON8138.cent⟩

end Certificates
