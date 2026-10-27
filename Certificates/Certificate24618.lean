module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13EDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
import Certificates.Kernel.Fin76bAut.Core2

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 in
theorem certificate24618 : ∀ {G : Type} [Group G] {E : Subgroup G} {t : G} {elt : ℕ → G},
    ELabelling E t mulE0 eT elt → EFacts613 E t :=
  fun hL => KernelFin76bAut.eFacts613_of_mulE0 hL

end Certificates
