module

public import CFSG.Quasithin.Vol2.KGFactC31HSData
import Certificates.Kernel.KGC31HS.Facts7219
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS CFSG.RankThree.Native in
theorem certificate7219 :
    (permOK (hs100Arr 0) = true) ∧ (permOK (hs100Arr 1) = true) ∧
    (permOK hs100FiveLines[0]! = true) ∧ (permOK hs100FiveLines[2]! = true) ∧
    (permOK hs100FiveLines[23]! = true) ∧
    (CFSG.Sporadic.Th.Native.invOK 100 aT (CFSG.Sporadic.Th.Native.invT 100 aT) = true) ∧ (CFSG.Sporadic.Th.Native.invOK 100 bT (CFSG.Sporadic.Th.Native.invT 100 bT) = true) ∧
    (ordTest 100 7 x7T = true) ∧ (ordTest 100 11 x11T = true) ∧
    (CFSG.Sporadic.Schreier.Native.conjTreeOK 100 genArr genInvArr b0T clA.1 clA.2.1 clA.2.2 = true) ∧
    (CFSG.Sporadic.Schreier.Native.conjTreeOK 100 genArr genInvArr rBT clB.1 clB.2.1 clB.2.2 = true) ∧
    (keysDistinct 100 clA.1.toList = true) ∧ (keysDistinct 100 clB.1.toList = true) ∧
    (clA.1.size = 5775) ∧ (clB.1.size = 15400) ∧
    (caChain.check = true) ∧ (caChain.orderCertificate = 7680) ∧
    (((tabsOf caGenW).all fun g => CFSG.Sporadic.Schreier.Native.commT 100 b0T g) = true) ∧
    (crChain.check = true) ∧ (crChain.orderCertificate = 2880) ∧
    (((tabsOf crGenW).all fun g => CFSG.Sporadic.Schreier.Native.commT 100 rBT g) = true) ∧
    (t0Chain.check = true) ∧ (t0Chain.orderCertificate = 512) ∧
    (countProducts 100 invCovered (levelTables t0Chain) (idT 100) = 512) := KernelKGC31HS.cert7219

end Certificates
