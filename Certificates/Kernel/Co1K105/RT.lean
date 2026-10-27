module

public import Certificates.Data.Kernel.Co1K105.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co1K105

@[expose] def rtb (i : Nat) : Bool := CFSG.KC.SLD2.rootsOK C D i

end CFSG.KD.Co1K105

#kss_each CFSG.KD.Co1K105.RT CFSG.KD.Co1K105.rtb 1

end
