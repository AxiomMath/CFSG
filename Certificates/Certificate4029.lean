module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Red0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4D4Data
public import CFSG.Sporadic.J4.BasicFacts
import Certificates.Kernel.J4Pent.Cover
public import CFSG.Sporadic.J4.QT2LocX0MainBase

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem certificate4029 : (∀ (p : Row) (v : ↥J), PentCand p v →
    ∃ k ∈ X0Sub, ∃ q ∈ {q : Row | ∃ w ∈ d4Reps.toList, q = toRow w.toVec}, p = k • q) ∧
    J4Basic := ⟨KernelJ4Pent.pent_cover,
    ⟨KernelJ4Q.matFacts, KernelJ4Count.card_Hj', KernelJ4Hub.card_J', fun x hx => by
      rw [← KernelJ4Pent.stab_w0]
      exact hx⟩⟩

end Certificates

namespace Certificates

open CertificateChecks

theorem certificate4029.basic : J4Basic := Certificates.certificate4029.2

end Certificates
