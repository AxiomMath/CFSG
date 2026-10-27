module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLCheckInputs
public meta import CFSG.Sporadic.SmallOddCore.McLLocalCheck
import Certificates.Kernel.LocalComp.McLCent

public section

open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.SmallOddCore
open CFSG.PSL3Four.Native

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd in
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native in
theorem certificate2024 : wordTabS 35 mclXGens (List.replicate 6 mclSixWord).flatten = idTab 35 ∧
    ∀ k ∈ [1, 2, 3, 4, 5],
      (wordTabS 35 mclXGens (List.replicate k mclSixWord).flatten == idTab 35) = false := by
  rw [KernelLC.McLC.mclXGens_eq]
  decide +kernel

end Certificates
