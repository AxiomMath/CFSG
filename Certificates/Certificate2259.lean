module

public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
import Certificates.Kernel.SporSch.Ru.Assemble2259
import Certificates.Kernel.SporSch.Ru.T2259P
import Certificates.Kernel.SporSch.Ru.T2259V0
import Certificates.Kernel.SporSch.Ru.T2259V1
import Certificates.Kernel.SporSch.Ru.T2259V2
import Certificates.Kernel.SporSch.Ru.T2259V3
import Certificates.Kernel.SporSch.Ru.T2259V4
import Certificates.Kernel.SporSch.Ru.T2259V5
import Certificates.Kernel.SporSch.Ru.T2259V6
import Certificates.Kernel.SporSch.Ru.T2259V7

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.Ru2259

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2259 : ruFixZ.length = 92 ∧ ruTreeSets.size = 593775 ∧
    (∀ j, 1 ≤ j → j < 593775 → ruTreeParent j < j ∧ ruTreeGen j < 2) ∧
    translatesOK ruTreeGens ruFixZ ruTreeSets ruTreePar ruTreeLab = true ∧
    ruSortedStrict ruTreeSets = true := by
  have of : ∀ m i, m ≤ i → blk (Nat.add m (i - m)) = true → blk i = true := by
    intro m i hm h
    have e : Nat.add m (i - m) = i := Nat.add_sub_cancel' hm
    rwa [e] at h
  have hb : ∀ i < 232, blk i = true := by
    intro i hi
    by_cases h1 : i < 29
    · exact of 0 i (Nat.zero_le i) (V0.all (i - 0) (by omega : i - 0 < 29))
    by_cases h2 : i < 58
    · exact of 29 i (by omega) (V1.all (i - 29) (by omega : i - 29 < 29))
    by_cases h3 : i < 87
    · exact of 58 i (by omega) (V2.all (i - 58) (by omega : i - 58 < 29))
    by_cases h4 : i < 116
    · exact of 87 i (by omega) (V3.all (i - 87) (by omega : i - 87 < 29))
    by_cases h5 : i < 145
    · exact of 116 i (by omega) (V4.all (i - 116) (by omega : i - 116 < 29))
    by_cases h6 : i < 174
    · exact of 145 i (by omega) (V5.all (i - 145) (by omega : i - 145 < 29))
    by_cases h7 : i < 203
    · exact of 174 i (by omega) (V6.all (i - 174) (by omega : i - 174 < 29))
    · exact of 203 i (by omega) (V7.all (i - 203) (by omega : i - 203 < 29))
  exact facts hb P.all

end Certificates

end
