module

public import CFSG.Quasithin.Vol2.KGFactC31M12Data
public import CFSG.Sporadic.Schreier.ImagePairs
import Certificates.Kernel.KGC31M12.Facts
import Certificates.Kernel.KGC31M12.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.M12Data
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.HeModelKSound
import CFSG.Certificates.Kernel.HexaKSound
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31.M12 in
theorem certificate7198 : ordTest 12 5 x5T = true ∧ ordTest 12 11 x11T = true ∧
    actCheck 12 5 (orderTables m12Certificate 2) (powTabs 12 x5T 5) = true ∧
    actCheck 12 11 (orderTables m12Certificate 2) (powTabs 12 x11T 11) = true := KernelKGC31M12.cert7198

end Certificates
