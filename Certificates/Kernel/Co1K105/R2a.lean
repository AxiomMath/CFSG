module

public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co1K105

@[expose] def r2a (i : Nat) : Bool := CFSG.KC.SLD2.rec2OK C D i

end CFSG.KD.Co1K105

#kss_each CFSG.KD.Co1K105.R2a CFSG.KD.Co1K105.r2a 8

end
