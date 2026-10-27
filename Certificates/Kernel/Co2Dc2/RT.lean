module

public import Certificates.Data.Kernel.Co2Dc2.Defs
public import Certificates.Data.Kernel.SporLatDc2Check
public import Certificates.Kernel.SporSch.Ru.RowsGen

public noncomputable section

namespace CFSG.KD.Co2Dc2

@[expose] def rtb (i : Nat) : Bool := CFSG.KC.SLD2.rootsOK C D i

end CFSG.KD.Co2Dc2

#kss_each CFSG.KD.Co2Dc2.RT CFSG.KD.Co2Dc2.rtb 28

end
