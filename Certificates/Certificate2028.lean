module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovalsInputs
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignSteiner3
import all CFSG.Monster.B.Classical.PlaneAut
meta import CFSG.Monster.B.Classical.PlaneData
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovalsInputs
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignHyperovalsInputs

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign
open CFSG.Monster.B.Classical.Plane

namespace CertificateChecks.Batch2028

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign
open CFSG.Monster.B.Classical.Plane

private theorem lineMasks_spec_0 : ∀ a x : Fin 21, (lineMasks[a.val]!).testBit x = decide (x ∈ projLine a) := by
  decide +kernel

private theorem arcs_listed_1 : ∀ x₀ x₁ : Fin 21, x₀ < x₁ → ArcLevel2 x₀ x₁ := by
  decide +kernel

private theorem class_facts_2 : hyperClass0.length = 56 ∧ hyperClass1.length = 56 ∧
    hyperClass2.length = 56 ∧ allHyper.Nodup ∧
    hyperClass0.all (fun X => hyperClass1.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
    hyperClass0.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
    hyperClass1.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true := by
  decide +kernel

private theorem delta_facts_3 : (∀ x, ofTable21 deltaInvTab (ofTable21 deltaTab x) = x) ∧
    (∀ x, ofTable21 deltaTab (ofTable21 deltaInvTab x) = x) ∧
    (∀ a : Fin 21, ∃ b : Fin 21, (projLine a).image (ofTable21 deltaTab) = projLine b) ∧
    hyperClass0.all (fun X => hyperClass1.contains (X.image (ofTable21 deltaTab))) = true ∧
    hyperClass1.all (fun X => hyperClass2.contains (X.image (ofTable21 deltaTab))) = true ∧
    hyperClass2.all (fun X => hyperClass0.contains (X.image (ofTable21 deltaTab))) = true := by
  decide +kernel

end CertificateChecks.Batch2028

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign in
open CFSG.Monster.B.Classical.Plane in
theorem certificate2028 : (∀ a x : Fin 21, (lineMasks[a.val]!).testBit x = decide (x ∈ projLine a))
    ∧ (∀ x₀ x₁ : Fin 21, x₀ < x₁ → ArcLevel2 x₀ x₁)
    ∧ (hyperClass0.length = 56 ∧ hyperClass1.length = 56 ∧
      hyperClass2.length = 56 ∧ allHyper.Nodup ∧
      hyperClass0.all (fun X => hyperClass1.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
      hyperClass0.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true ∧
      hyperClass1.all (fun X => hyperClass2.all fun Y => (X ∩ Y).card % 2 == 1) = true
    )
    ∧ ((∀ x, ofTable21 deltaInvTab (ofTable21 deltaTab x) = x) ∧
      (∀ x, ofTable21 deltaTab (ofTable21 deltaInvTab x) = x) ∧
      (∀ a : Fin 21, ∃ b : Fin 21, (projLine a).image (ofTable21 deltaTab) = projLine b) ∧
      hyperClass0.all (fun X => hyperClass1.contains (X.image (ofTable21 deltaTab))) = true ∧
      hyperClass1.all (fun X => hyperClass2.contains (X.image (ofTable21 deltaTab))) = true ∧
      hyperClass2.all (fun X => hyperClass0.contains (X.image (ofTable21 deltaTab))) = true
    ) := by
  exact ⟨CertificateChecks.Batch2028.lineMasks_spec_0, CertificateChecks.Batch2028.arcs_listed_1, CertificateChecks.Batch2028.class_facts_2, CertificateChecks.Batch2028.delta_facts_3⟩

end Certificates
