module

public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co1K105

@[expose] def fr0 (i : Nat) : Bool := CFSG.KC.SLD2.fRowOK C D (Nat.add 0 i)

end CFSG.KD.Co1K105

#kss_each CFSG.KD.Co1K105.F0 CFSG.KD.Co1K105.fr0 8

end
