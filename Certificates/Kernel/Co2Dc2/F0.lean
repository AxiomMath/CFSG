module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co2Dc2

@[expose] def fr0 (i : Nat) : Bool := CFSG.KC.SLD2.fRowOK C D (Nat.add 0 i)

end CFSG.KD.Co2Dc2

#kss_each CFSG.KD.Co2Dc2.F0 CFSG.KD.Co2Dc2.fr0 2

end
