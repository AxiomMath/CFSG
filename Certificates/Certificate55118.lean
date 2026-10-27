module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Data.E4QuatO8Check
import Certificates.Kernel.OmegaEight.E4O8SgGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.TL4.E4O8 in
theorem certificate55118 : ∀ y : Equiv.Perm (Fin 360),
    (∃ s ∈ [1, gen 8, gen 8 * gen 8, gen 9, gen 9 * gen 8, gen 9 * (gen 8 * gen 8)],
      s⁻¹ * y ∈ omegaT) →
    y * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * y →
    y * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * y → y * y = 1 →
    ∀ g ∈ omegaT, g * mainPerm 0 = mainPerm 0 * g →
    (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom ≠
      Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())} →
    ∀ w ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom,
    (∀ b ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj g).toMonoidHom, y * b * y⁻¹ = w * b * w⁻¹) →
    ∃ d ∈ omegaT, d * mainPerm 0 = mainPerm 0 * d ∧
      (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
          (MulAut.conj d).toMonoidHom ≠
        Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())} ∧
      ∀ b ∈ (Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())}).map
        (MulAut.conj d).toMonoidHom, y * b = b * y := KernelO8.E4C.e4c_sg

end Certificates
