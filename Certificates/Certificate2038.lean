module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUniqueInputs
public meta import CFSG.Monster.B.Classical.PlaneData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneFrame
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquares
import all CFSG.Monster.B.Classical.PlaneIncidence
import all CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUniqueInputs
meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneUniqueInputs

public section

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign Equiv
open CFSG.Monster.B.Classical.Plane

namespace CertificateChecks.Batch2038

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign Equiv
open CFSG.Monster.B.Classical.Plane

private theorem vlineImage_mem_0 : ∀ j : Fin 5,
    insert 0 (Finset.univ.image (enc j)) ∈ Finset.univ.image projLine := by
  decide +kernel

private theorem tlineImage_mem_1 : ∀ x y : Fin 4,
    ({enc 0 x, enc 1 y, enc 2 (latinSq rA x y), enc 3 (latinSq rB x y),
      enc 4 (latinSq rC x y)} : Finset (Fin 21)) ∈ Finset.univ.image projLine := by
  decide +kernel

end CertificateChecks.Batch2038

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign Equiv in
open CFSG.Monster.B.Classical.Plane in
theorem certificate2038 : (∀ j : Fin 5,
      insert 0 (Finset.univ.image (enc j)) ∈ Finset.univ.image projLine
    )
    ∧ (∀ x y : Fin 4,
      ({enc 0 x, enc 1 y, enc 2 (latinSq rA x y), enc 3 (latinSq rB x y),
        enc 4 (latinSq rC x y)} : Finset (Fin 21)) ∈ Finset.univ.image projLine
    ) := by
  exact ⟨CertificateChecks.Batch2038.vlineImage_mem_0, CertificateChecks.Batch2038.tlineImage_mem_1⟩

end Certificates
