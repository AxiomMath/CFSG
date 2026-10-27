module

public import Certificates.Data.RudvalisFF81Sp8Torus
import Certificates.Kernel.Misc.Sp8Syl3.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8 in
theorem certificate899103 : pairsChk899103 = true ∧ e0Chk899103 = true ∧ pChk899103 = true ∧ cpChk899103 = true ∧
    conjChk899103 = true :=
  CFSG.KD.Sp8Syl3.cert899103_ok

end Certificates
