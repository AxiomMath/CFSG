module

public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co1K105

@[expose] def r1a (i : Nat) : Bool := CFSG.KC.SLD2.rec1OK C D (D.R1.getD i default)

end CFSG.KD.Co1K105

#kss_each CFSG.KD.Co1K105.R1a CFSG.KD.Co1K105.r1a 8

end
