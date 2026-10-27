module

public import Certificates.Data.RudvalisFF81Sp8Cent
import Certificates.Kernel.Misc.Sp8Cz.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8 in
theorem certificate899105 : czChk899105 = true ∧ colChk899105 = true ∧ e0cChk899105 = true ∧ hypChk899105 = true ∧
    f1Chk899105 = true ∧ e9Chk899105 = true :=
  CFSG.KD.Sp8Cz.cert899105_ok

end Certificates
