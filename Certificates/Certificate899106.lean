module

public import Certificates.Data.RudvalisFF81Sp8Sylow2
import Certificates.Kernel.Misc.Sp8U0.FinalCov

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp8 in
theorem certificate899106 : u0Chk899106 = true ∧ zuChk899106 = true ∧ baseChk899106 = true ∧ covChk899106 = true :=
  ⟨CFSG.KD.Sp8U0.u06_u0Chk, CFSG.KD.Sp8U0.u06_zuChk, CFSG.KD.Sp8U0.u06_baseChk,
    CFSG.KD.Sp8U0.u06_covChk⟩

end Certificates
