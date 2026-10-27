module

public import Certificates.Data.Kernel.PermCent.CentK6C

public section

namespace Certificates.Kernel.CentKFin

open CFSG.Certificates.Kernel.PkCV

theorem c6F_true : c6F = true := by
  decide +kernel

theorem f5F_true : f5F = true := by
  decide +kernel

end Certificates.Kernel.CentKFin

end
