module

public import Certificates.Data.Sylow185.U38
import Certificates.Kernel.U38R.ElimGlue

public section

namespace Certificates

open CertificateChecks

theorem certificate185001 : CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim.check () = true :=
  KernelU38R.check_R

end Certificates
