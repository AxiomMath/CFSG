module

public import Certificates.Data.Kernel.Fi22.Letters

public section

namespace CFSG.KS.Fi22N

open CFSG.KC.Enum CFSG.KS.Fi22L

@[expose] def nuText : String := include_str "nfpu.hex"

@[expose] noncomputable def nuPacked : Nat := by hex_nat nuText 10530 11965276352394084973

@[expose] noncomputable def UK (x : Nat) : Nat := lk nuPacked x

end CFSG.KS.Fi22N

end
