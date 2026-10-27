module

public import Certificates.Data.McLFiveTables
public import CFSG.Sporadic.SmallOddCore.McLData
import Certificates.Kernel.ThFamC.K19766

public section

namespace Certificates

open CertificateChecks

theorem certificate19766 : CFSG.Sporadic.Schreier.mclStrongArrs[0]! = Certificates.MaxD2Heis.mclTabA ∧
    CFSG.Sporadic.Schreier.mclStrongArrs[1]! = Certificates.MaxD2Heis.mclTabB ∧
    CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl =
      Certificates.MaxD2Heis.mclTabU ∧
    Certificates.MaxD2Heis.mclTabA.size = 275 ∧ Certificates.MaxD2Heis.mclTabB.size = 275 ∧
    Certificates.MaxD2Heis.mclTabU.size = 275 := KernelThFamC.K19766.facts

end Certificates
