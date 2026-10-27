module

public import Certificates.Data.FF81Sp6Cls
import Certificates.Kernel.Sp6Cls.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls in
theorem certificate899111 : pairsChk899111 = true ∧ c7Chk899111 = true ∧ witChk899111 = true ∧
    sylChk899111 = true :=
  CFSG.KD.Sp6Cls.facts

end Certificates
