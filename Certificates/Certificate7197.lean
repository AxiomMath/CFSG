module

public import CFSG.Quasithin.Vol2.KGFactC31M11Data
public import CFSG.Sporadic.Schreier.ImagePairs
import Certificates.Kernel.KGC31M11.Facts
import Certificates.Kernel.KGC31M11.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.M11Data
import CFSG.Certificates.Kernel.BfsPinSound
import CFSG.Certificates.Kernel.HeModelKSound
import CFSG.Certificates.Kernel.HexaKSound
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31.M11 in
theorem certificate7197 : ordTest 11 5 x5T = true ∧ ordTest 11 11 x11T = true ∧
    actCheck 11 5 (orderTables m11Certificate 2) (powTabs 11 x5T 5) = true ∧
    actCheck 11 11 (orderTables m11Certificate 2) (powTabs 11 x11T 11) = true := KernelKGC31M11.cert7197

end Certificates
