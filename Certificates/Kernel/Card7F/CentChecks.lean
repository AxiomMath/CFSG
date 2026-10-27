module

public import Certificates.Data.Kernel.PermCent.F7Cent

public section

namespace Certificates.Kernel.Card7F

open Equiv CFSG.Certificates.Kernel.PkCV

theorem cent_f0_g0 :
    decide ((CF7 (cOf (swap 0 1 * swap 1 2 : Perm (Fin 7)))).length = 288 ∧
      (CF7 (cOf (swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5) : Perm (Fin 7)))).length = 72) = true := by
  decide +kernel

end Certificates.Kernel.Card7F

end
