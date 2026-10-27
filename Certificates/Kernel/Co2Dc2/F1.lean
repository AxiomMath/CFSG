module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co2Dc2

@[expose] def fr1 (i : Nat) : Bool := CFSG.KC.SLD2.fRowOK C D (Nat.add 2 i)

end CFSG.KD.Co2Dc2

#kss_each CFSG.KD.Co2Dc2.F1 CFSG.KD.Co2Dc2.fr1 2

end
