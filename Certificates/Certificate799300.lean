module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Inputs
public meta import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Inputs
import CFSG.Certificates.Kernel.U33PairSound
import Certificates.Kernel.U33Pair.Check
public meta import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Prod

public section

namespace Certificates

open CertificateChecks

theorem certificate799300 : CFSG.RankThree.PartTwo.Sec8.Hering88F.u33TwoTransOK () = true :=
  CFSG.KC.U33Pair.u33TwoTransOK_of_pairsK _ KernelU33Pair.u33Codes_length
    KernelU33Pair.u33Pairs_ok

end Certificates
