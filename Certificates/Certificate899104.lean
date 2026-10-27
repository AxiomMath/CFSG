module

public import Certificates.Data.RudvalisFF81Sp8Norm
import Certificates.Kernel.Misc.Sp8N0.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8 in
theorem certificate899104 : n0Chk899104 = true ∧ fixChk899104 = true ∧ clsChk899104 = true ∧ normChk899104 = true ∧
    prodChk899104 = true :=
  CFSG.KD.Sp8N0.cert899104_ok

end Certificates
