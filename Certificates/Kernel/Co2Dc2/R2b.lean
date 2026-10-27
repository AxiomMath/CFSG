module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co2Dc2

@[expose] def r2b (i : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D (Nat.add 16 i)

end CFSG.KD.Co2Dc2

#kss_each CFSG.KD.Co2Dc2.R2b CFSG.KD.Co2Dc2.r2b 16

end
