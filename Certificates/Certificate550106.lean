module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeClasses
public import Certificates.Data.E4QuatO8Check
import Certificates.Kernel.OmegaEight.E4O8CentGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.TL4.E4O8 in
theorem certificate550106 : ∀ a ∈ omegaT, a * a = 1 → a ≠ 1 → a ≠ mainPerm 0 →
    a * permOfArr 360 (u0A ()) = permOfArr 360 (u0A ()) * a →
    a * permOfArr 360 (v0A ()) = permOfArr 360 (v0A ()) * a →
    ∃ c ∈ omegaT, c ^ 3 = 1 ∧ c * mainPerm 0 = mainPerm 0 * c ∧ c * a ≠ a * c := KernelO8.E4C.e4c_move

end Certificates
