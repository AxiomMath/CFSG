module

public import CFSG.Quasithin.Vol2.KGFactC31J2Data
public import CFSG.Sporadic.Schreier.ImagePairs
import Certificates.Kernel.KGC31J2.Facts
import Certificates.Kernel.KGC31J2.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31ActCheck
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.J2 in
theorem certificate7199 : ordTest 315 5 x5aT = true ∧ ordTest 315 5 x5bT = true ∧ ordTest 315 7 x7T = true ∧
    tblEq 315 (compT 315 x5aT x5bT) (compT 315 x5bT x5aT) = true ∧
    gridInj 315 x5aT x5bT 5 = true ∧
    actCheck 315 5 invTabs (gridTabs 315 x5aT x5bT 5 5) = true ∧
    actCheck 315 7 invTabs (powTabs 315 x7T 7) = true := KernelKGC31J2.cert7199

end Certificates
