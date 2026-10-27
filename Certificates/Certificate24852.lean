module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData
import CFSG.Certificates.Kernel.OctadBigSound
import Certificates.Kernel.OctadBig.Checks
import Certificates.Kernel.Compat.Checks

public section

namespace Certificates

theorem certificate24852 : CFSG.EvenSporadicStandard.M24Std.OctadBigData :=
  CFSG.KC.OctadBig.octadBig_of CFSG.KD.LQT.C4137.hG
    (CFSG.KC.Compat.compat_of CFSG.KD.LQT.C4137.hG CFSG.KD.Compat.ch24853).1
    CFSG.KD.OctadBig.ch24852

end Certificates
