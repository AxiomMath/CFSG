module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

@[expose] def SqData.asData (D : SqData) : Data :=
  { seedA := D.seedA, seedB := D.seedB, nregs := D.nregs, prog := D.prog,
    outs := [D.rx, D.ry, D.rh], tests := [D.t] }

end CFSG.SectionRank.Native

end
