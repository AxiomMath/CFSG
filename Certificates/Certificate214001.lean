
module

public import CFSG.LieType.ChevTwo.InversionCheck
import CFSG.LieType.ChevTwo.InversionMath

public section

namespace Certificates

theorem certificate214001 : ∀ v : Fin 16 → ZMod 2, CFSG.LieType.ChevTwo.GL4Native.chk (List.ofFn v) = true :=
  CFSG.LieType.ChevTwo.GL4Math.chk_all_math

end Certificates
