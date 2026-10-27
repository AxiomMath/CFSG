module

public import Certificates.Data.G23RecogNativeInputs
public import Certificates.Data.G23RecogWordsInputs
import Certificates.Kernel.G23Code.Checks
import CFSG.Certificates.Kernel.G23Code.Sound

public section

namespace Certificates

open CertificateChecks.KernelG23C

open CFSG.GH74.QTGen4.Recog.G23 CFSG.RankThree.PartTwo.Census.Carrier.G2Three in
theorem certificate320001 : (∀ i, mul14 (CFSG.GH74.QTGen4.Recog.G23.eCode i) (eInvCode i) = one14)
    ∧ (∀ r ∈ g23Words, evalCode r = one14) := by
  have hI : ∀ i, CFSG.KD.G23C.invChk i = true := by
    intro i
    fin_cases i
    · exact inv_ok0
    · exact inv_ok1
    · exact inv_ok2
    · exact inv_ok3
    · exact inv_ok4
    · exact inv_ok5
  exact ⟨CFSG.KS.G23C.inv_sound consts_ok hI, CFSG.KS.G23C.rels_sound consts_ok hI words_ok⟩

end Certificates
