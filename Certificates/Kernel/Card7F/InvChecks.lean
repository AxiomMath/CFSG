module

public import Certificates.Data.Kernel.PermCent.F7CentChk

public section

namespace Certificates.Kernel.Card7F

open Equiv CFSG.Certificates.Kernel.PkCV

theorem inv_chk :
    f7InvChkAt (cOf (swap 0 1 * swap 1 2 : Perm (Fin 7)))
      (cOf (swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5) : Perm (Fin 7))) = true := by
  decide +kernel

end Certificates.Kernel.Card7F

end
