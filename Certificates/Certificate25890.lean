module

public import CFSG.Sporadic.SmallOddCore.J3Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Data
import Certificates.Kernel.Sporadic.OddCore.J3OutX25890Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier in
theorem certificate25890 : ∀ {Y : Type} [Group Y] [Finite (MulAut Y)] (φ : Equiv.Perm (Fin 6156) → MulAut Y) (t : Y),
    t * t = 1 → t ≠ 1 →
    (∀ x ∈ j3S, ∀ y ∈ j3S, φ (x * y) = φ x * φ y) →
    (∀ x ∈ j3S, ∀ y ∈ j3S, φ x = φ y → x = y) →
    φ (CFSG.Sporadic.SmallOddCore.tp 6156 (j3CentTbl 9)) = MulAut.conj t →
    (∀ x ∈ j3S, x ∈ j3P → ∃ y : Y, φ x = MulAut.conj y) →
    (∀ x ∈ j3S, x ∈ j3P → x * x = 1 → x ≠ 1 → ∃ c : Y, φ x = MulAut.conj (c * t * c⁻¹)) →
    ∃ K E : Subgroup (MulAut Y), OuterEFacts Y K t E :=
  fun φ t => KernelSpor.J3OutX25890.outerFacts25890 φ t

end Certificates
