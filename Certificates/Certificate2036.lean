module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUnique
public import CFSG.Monster.B.Classical.PlaneAut
public meta import CFSG.Monster.B.Classical.PlaneData
public import Certificates.Certificate2037
public import Certificates.Certificate2038
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUnique
import all CFSG.Monster.B.Classical.PlaneAut

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign CFSG.Fischer
open CFSG.Monster.B.Classical.Plane Module

namespace CertificateChecks.Batch2036

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign CFSG.Fischer
open CFSG.Monster.B.Classical.Plane Module

private theorem isSteinerPlane_projLine_card_line_0 : ∀ a : Fin 21, projLine a ∈ Finset.univ.image projLine → (projLine a).card = 5 := by
  decide +kernel

private theorem isSteinerPlane_projLine_key_1 : ∀ x y : Fin 21, x ≠ y → ∃ a : Fin 21, (x ∈ projLine a ∧ y ∈ projLine a) ∧
    ∀ b : Fin 21, x ∈ projLine b ∧ y ∈ projLine b → b = a := by
  decide +kernel

end CertificateChecks.Batch2036

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign CFSG.Fischer in
open CFSG.Monster.B.Classical.Plane Module in
theorem certificate2036 : (∀ a : Fin 21, projLine a ∈ Finset.univ.image projLine → (projLine a).card = 5)
    ∧ (∀ x y : Fin 21, x ≠ y → ∃ a : Fin 21, (x ∈ projLine a ∧ y ∈ projLine a) ∧
      ∀ b : Fin 21, x ∈ projLine b ∧ y ∈ projLine b → b = a
    ) := by
  exact ⟨CertificateChecks.Batch2036.isSteinerPlane_projLine_card_line_0, CertificateChecks.Batch2036.isSteinerPlane_projLine_key_1⟩

end Certificates
