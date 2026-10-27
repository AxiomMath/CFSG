module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmegaDefs
import CFSG.Certificates.Kernel.QdOmegaSound
import Certificates.Kernel.QdOmega.Checks
import Certificates.Data.Kernel.QdOmega
import Certificates.Kernel.LocalQT.Syl.C4137
import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sym6Sq.Checks
import Certificates.Certificate4137
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

theorem certificate24848 : CFSG.EvenSporadicStandard.M24Std.QdOmegaData :=
  CFSG.KC.QdOm.qdOmegaData_of CFSG.KD.LQT.C4137.hG CFSG.KD.Sym6Sq.ch25731om
    CFSG.KD.QdOm.ch24848om
    (CFSG.KC.QdOm.qdEnum_of CFSG.KD.QdOm.ch24848e1 CFSG.KD.QdOm.ch24848e2
      CFSG.KD.QdOm.ch24848cov)

end Certificates
