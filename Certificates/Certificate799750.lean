module

public import Certificates.Data.FF81Am6LSide
import Certificates.Kernel.LSide.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData in
theorem certificate799750 : lsideCheck = true :=
  CFSG.KD.LSide.lside_ok

end Certificates
