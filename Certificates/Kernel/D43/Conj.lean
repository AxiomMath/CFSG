module

public import Certificates.Data.Kernel.D43.Conj
public import Certificates.Kernel.D43.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43

theorem conj_all : (List.range 8).all (fun k => conjOK RL k (conjW.getD k [])) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
