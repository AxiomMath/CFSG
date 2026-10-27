module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om
import Certificates.Kernel.J4M2.C7951

public section

namespace Certificates

open CertificateChecks

theorem certificate7951 : ∀ i, 0 < i → i < 77 → ∃ c ∈ [133, 778, 911, 1131, 1262, 1889, 2020],
    (CFSG.Quasithin.J4M2.ptElt i)⁻¹ * CFSG.Sporadic.J4.QT.eta CFSG.Sporadic.J4.QT.uJ 11 c *
      CFSG.Quasithin.J4M2.ptElt i ∉ CFSG.Sporadic.J4.QT.Eg CFSG.Sporadic.J4.QT.uJ 11 := KernelJ4M2.c7951

end Certificates
