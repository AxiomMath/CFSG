module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.SchreierFam.C5139K
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum

open CFSG in
open CFSG CFSG.Certificates CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG.ComponentClassification.OuterAutomorphisms in
theorem certificate5139 : (((enumeration m22OutCentQ1).any fun u => (enumeration m22OutCentQ1).any fun v =>
      decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true)
    ∧ (((enumeration m22OutCentQ2).any fun u => (enumeration m22OutCentQ2).any fun v =>
      decide (u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u)) = true) := by
  rw [← elemsT_eq, ← elemsT_eq, elemsT_eq_elemsV, elemsT_eq_elemsV]
  exact ⟨KernelSchreierFam.q1_5139K, KernelSchreierFam.q2_5139K⟩

end Certificates
