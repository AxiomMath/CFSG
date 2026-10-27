module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2J2Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Data
import Certificates.Kernel.J2Cover.OuterX25880Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2TableDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.J2
  CFSG.ComponentClassification.J2Cover.Models in
theorem certificate25880 : (∀ {Y : Type} [Group Y] [Finite (MulAut Y)] (elt : ℕ → MulAut Y) (t : Y),
      t * t = 1 → t ≠ 1 →
      (∀ a b, a < 256 → b < 256 → elt a = elt b → a = b) →
      (∀ a b, a < 256 → b < 256 → mulX a b < 256 ∧ elt a * elt b = elt (mulX a b)) →
      elt 0 = 1 → elt 4 = MulAut.conj t →
      (∀ a, a < 128 → ∃ y : Y, elt a = MulAut.conj y) →
      (∀ a ∈ TableX.eListX 256 innX mulX 4, mulX a a = 0 → a ≠ 0 →
        ∃ c : Y, elt a = MulAut.conj (c * t * c⁻¹)) →
      ∃ K E : Subgroup (MulAut Y), OuterEFacts Y K t E) ∧
    ∀ a ∈ TableX.eListX 256 innX mulX 4,
      a < 128 ∧ (mulX a a = 0 → a ≠ 0 → fixCountArr eltArrs[a]! = 11) :=
  ⟨KernelJ2Cover.outerFacts25880, KernelJ2Cover.fixFacts25880⟩

end Certificates
