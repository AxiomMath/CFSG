module

public import Certificates.Data.Kernel.PermCent.A7AiC

public section

namespace Certificates.Kernel.A7Ai

open CFSG.Certificates.Kernel.PkCV

theorem a7aiAF_true : a7aiAF = true := by
  decide +kernel

theorem a7aiBF_true : a7aiBF = true := by
  decide +kernel

end Certificates.Kernel.A7Ai

end
