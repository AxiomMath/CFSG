module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs
import Certificates.Kernel.LocalComp.Co3IdentData

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3 in
theorem certificate3089 : (∀ i < 7, isInvA 276 (genArr i) (invCand 276 (genArr i)) = true) ∧
      (∀ i ∈ mLetters, siftA 276 co3MLevels co3MBaseArr 0 (genArr i) = true) ∧
      siftA 276 co3ChainLevels co3ChainBaseArr 0 (genArr 3) = true ∧
      eqA 276 (compA 276 (genArr 3) (genArr 3)) (idA 276) = true ∧
      eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 4) (genArr 3))) (genArr 0) = true ∧
      eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 0) (genArr 3))) (genArr 4) = true ∧
      eqA 276 (compA 276 (genArr 0) (genArr 2)) (compA 276 (genArr 2) (genArr 0)) = true := KernelLC.Co3Id.facts

end Certificates
