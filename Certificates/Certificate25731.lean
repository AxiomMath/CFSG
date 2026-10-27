module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSqCheck
import CFSG.Certificates.Kernel.Sym6SqSound
import Certificates.Kernel.Sym6Sq.Checks
import Certificates.Data.Kernel.Sym6Sq
import Certificates.Kernel.LocalQT.Syl.C4137
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate4137
import Certificates.Certificate24864
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.Certificates.Kernel.LocalQTSyl24Sound
import CFSG.Certificates.Kernel.LocalQTSylSound

public section

namespace Certificates

theorem certificate25731 : CFSG.EvenSporadicStandard.M24Std.Sym6.Sym6SqData :=
  CFSG.KC.Sym6Sq.sym6SqData_of CFSG.KD.LQT.C4137.hG CFSG.KD.Sym6Sq.ch25731om
    CFSG.KD.Sym6Sq.ch25731sq

end Certificates
