module

public import Certificates.Data.YamakiS7
import Certificates.Kernel.Misc.YamakiS7
import CFSG.Certificates.Kernel.Misc.YamakiS7Sound

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki in
theorem certificate550881 : s7Check () = true :=
  CFSG.KC.YamakiS7.s7Check_of_s7K KernelYamakiS7.s7K_true

end Certificates
