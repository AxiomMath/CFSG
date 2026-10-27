module

public import Certificates.Data.Item434G28R
import Certificates.Kernel.G28.Glue9549

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Item434G28 in
theorem certificate9549 : ∀ R : Submonoid (Matrix (Fin 6) (Fin 6) CFSG.Quasithin.GF8),
    R = Submonoid.closure {x | ∃ g ∈ rGens, dec2 g = x} →
    (∀ e ∈ R, ∀ y ∈ R, e ^ 3 = 1 → e ≠ 1 → y ^ 7 = 1 → y ≠ 1 → e * y ≠ y * e) ∧
    (∀ e ∈ R, ∀ t ∈ R, ∀ t' ∈ R, e ^ 3 = 1 → e ≠ 1 → t ^ 2 = 1 → t ≠ 1 → t' ^ 2 = 1 →
      t' ≠ 1 → t ≠ t' → t * e = e * t → t' * e = e * t' → t * t' = t' * t → False) ∧
    (∀ e ∈ R, ∀ u ∈ R, ∀ t ∈ R, e ^ 3 = 1 → e ≠ 1 → u ^ 3 = 1 → u ≠ 1 → u ≠ e →
      u ≠ e * e → t ^ 2 = 1 → t ≠ 1 → t * e = e * t → t * u = u * t → u * e = e * u → False) ∧
    decode (letterCode (8 * 5 + 1)) = dec2 rGenXb ∧ decode (letterCode (8 * 0 + 1)) = dec2 rGenXa ∧
    decode (letterCode (8 * 6 + 1)) = dec2 rGenYa ∧ decode (letterCode (8 * 11 + 1)) = dec2 rGenYb := KernelG28.R9549.proof9549

end Certificates
