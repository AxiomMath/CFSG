module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Data.E4QuatO8Check
import Certificates.Kernel.OmegaEight.E4O8CentGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.TL4.E4O8 in
theorem certificate55116 : ∀ x ∈ omegaT, x * mainPerm 0 = mainPerm 0 * x → (∃ k : ℕ, x ^ 3 ^ k = 1) → x ≠ 1 →
    ∃ y ∈ omegaT, y ^ 3 = 1 ∧ y * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * y ∧
      y * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * y ∧ x * y ≠ y * x := KernelO8.E4C.e4c_noGood

end Certificates
