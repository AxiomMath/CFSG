module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45Data
import Certificates.Kernel.MaxD2.McLP.Lem45Glue
public import Certificates.Data.McLFiveLocalP

public section

namespace Certificates

open CertificateChecks

theorem certificate320016 : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45.check
    Certificates.MaxD2Heis.mclFiveDataP
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45.wordW
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLLem45.tree = true := KernelMaxD2.McLP.mcl_lem45

end Certificates
