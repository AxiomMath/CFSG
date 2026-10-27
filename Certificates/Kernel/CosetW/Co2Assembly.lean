module

public import CFSG.Certificates.Kernel.CosetW.Columns
public import CFSG.Sporadic.Co2Smith.GlWInputs
import Certificates.Kernel.CosetW.Co2SmithW

public section

open CFSG.CosetTable CFSG.Sporadic.Co2Smith.Native

namespace CertificateChecks.CosetW

theorem proof21167 :
    subsetCheckC (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) glWRels) [] 100000 1440 = true ∧
      subsetCheckC glWRels [0, 1, 2, 3, 4, 5] 100000 36 = true := by
  refine ⟨?_, ?_⟩
  · rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
    exact glW_e1_checkW
  · rw [subsetCheckC_eq_checkW _ _ (by decide +kernel)]
    exact glW_e2_checkW

end CertificateChecks.CosetW
