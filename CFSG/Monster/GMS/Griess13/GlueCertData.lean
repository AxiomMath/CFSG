module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_decls CFSG.Monster.GMS.Griess13.GlueCert "CFSG/Monster/GMS/Griess13/data/gluecert.txt" 178007 12768317681489848343

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def certTab (a : Nat) : Nat × Nat := (GlueCert.mu.getD a 0, GlueCert.lam.getD a 0)

end CFSG.Monster.GMS.Griess13.Co1Data

end
