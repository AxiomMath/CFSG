module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.OrderFour
public import CFSG.RankThree.PartOne.KS.HeSevenData
import Certificates.Kernel.HeLoc.SevenOrd4Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate17300 : CFSG.HardMathSupport.Dickson.I271.orderFourOK 8330
    CFSG.RankThree.PartOne.heSevenC1Gens[2]! = true := KernelHeLoc.Seven.orderFour

end Certificates
