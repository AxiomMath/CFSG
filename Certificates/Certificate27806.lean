module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EQDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import Certificates.Kernel.Fin76bAut.Core2
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWIso2

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 in
theorem certificate27806 : (∀ {G : Type} [Group G] {E : Subgroup G} {t : G} {elt : ℕ → G},
      ELabelling E t mulE0 CFSG.EvenSporadicStandard.Fin76b.W16.eT elt → EFactsQ E t) ∧
    ∀ {G : Type} [Group G] {E : Subgroup G} {t : G} {elt : ℕ → G},
      ELabelling E t mulEJ3 CFSG.EvenSporadicStandard.Fin76b.W16.eT elt → EFactsQ E t :=
  ⟨fun hL => KernelFin76bAut.eFactsQ_of_mulE0 hL, fun hL => KernelFin76bAut.eFactsQ_of_mulE0
    (CFSG.EvenSporadicStandard.Fin76b.W16.eLab_of_J3 hL)⟩

end Certificates
