module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HeE8Check
import Certificates.Kernel.He27143.Final

public section

namespace Certificates

theorem certificate27143 : CFSG.EvenSporadicStandard.Induction.heE8Check
    (CFSG.Sporadic.He.Native.orbitData ()) = true := CFSG.KD.HeTab.heE8_ok

end Certificates
