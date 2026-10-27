module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelCheck
import Certificates.Kernel.EvenSporCSide.Facts
import Certificates.Kernel.EvenSporCSide.Rep5

public section

open CFSG.EvenSporadicStandard.HNRecog.CSide CertificateChecks.KernelCSide

namespace CertificateChecks.Batch442021

open CFSG.EvenSporadicStandard.HNRecog.CSide CertificateChecks.KernelCSide

theorem rep5 : cSideRep5 := by
  unfold cSideRep5
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _
  rw [cSideB5_all g]
  decide

theorem cSideModel_0 : cSideModelOK = true := by
  simp only [cSideModelOK, k6a, k6c, k4a, k4d, rep4b, rep4c, k3, k1, k2, rep5, decide_true,
    Bool.and_self]

end CertificateChecks.Batch442021

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.HNRecog.CSide in
theorem certificate442021 : cSideModelOK = true :=
  CertificateChecks.Batch442021.cSideModel_0

end Certificates
