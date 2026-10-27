module

public import CFSG.Quasithin.Vol2.KGFactC31M24Data
import Certificates.Kernel.KGC31M24.Facts7217
import Certificates.Kernel.KGC31M24.Defs7217
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.Vol2.KGFactC31CosetCheck
public import CFSG.Quasithin.Vol2.KGFactC31FrameCheck
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Certificates in
theorem certificate7217 :
    ((tblEq 24 b0T (toTable (m24InvReps.getD 1 1))) &&
      (tblEq 24 b1T (toTable (m24InvReps.getD 0 1))) && (ebasisOK 24 CFSG.Quasithin.KGC31.M24.oT) && (ebasisOK 24 sT) &&
      (ebasisOK 24 s16T) && (ebasisOK 24 s32T) && (ebasisOK 24 r2T) && (ebasisOK 24 u4T) &&
      (ebasisOK 24 u5T) && (ebasisOK 24 u6T) && (ebasisOK 24 tT) && (ebasisOK 24 etT)) = true ∧
    ((cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 CFSG.Quasithin.KGC31.M24.oT) == 16) && (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 sT) == 64) &&
      (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 s16T) == 64) && (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 s32T) == 64) &&
      (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 r2T) == 16) && (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 u4T) == 16) &&
      (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 u5T) == 128) && (cb0T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 tT) == 64) &&
      (cb1T.countP (CFSG.Sporadic.Schreier.Native.commAll 24 u6T) == 64)) = true ∧
    ((sT.all (CFSG.Sporadic.Schreier.Native.commAll 24 s16T)) && (sT.all (CFSG.Sporadic.Schreier.Native.commAll 24 s32T)) && (CFSG.Sporadic.Th.Native.invOK 24 d4T (CFSG.Sporadic.Th.Native.invT 24 d4T)) &&
      ((CFSG.Quasithin.KGC31.M24.conjAll d4T r2T).all (CFSG.Sporadic.Schreier.Native.commAll 24 u4T)) && (CFSG.Sporadic.Th.Native.invOK 24 d6T (CFSG.Sporadic.Th.Native.invT 24 d6T)) &&
      ((CFSG.Quasithin.KGC31.M24.conjAll d6T tT).all (CFSG.Sporadic.Schreier.Native.commAll 24 u6T)) &&
      (qGen.all fun g => CFSG.Sporadic.Schreier.Native.commAll 24 u5T (toTable g))) = true ∧
    (moChain.check && (moChain.orderCertificate == 322560) && nsChain.check &&
      (nsChain.orderCertificate == 138240) && lsChain.check &&
      (lsChain.orderCertificate == 69120) && qChain.check && (qChain.orderCertificate == 128) &&
      nqChain.check && (nqChain.orderCertificate == 21504) && lqChain.check &&
      (lqChain.orderCertificate == 10752) && ntChain.check && (ntChain.orderCertificate == 64512) &&
      kqChain.check && (kqChain.orderCertificate == 21504)) = true ∧
    (((moGen.zip moMasks).all (fun p => masksOK 24 CFSG.Quasithin.KGC31.M24.oT (toTable p.1) p.2)) &&
      ((nsGen.zip nsMasks).all (fun p => masksOK 24 sT (toTable p.1) p.2)) &&
      (masksOK 24 sT y5T y5Masks) && ((njT.zip njMasks).all (fun p => masksOK 24 sT p.1 p.2)) &&
      ((nqGen.zip nqMasks).all (fun p => masksOK 24 u5T (toTable p.1) p.2)) &&
      (masksOK 24 u5T y7T y7Masks) && ((mjT.zip mjMasks).all (fun p => masksOK 24 u5T p.1 p.2)) &&
      ((ntGen.zip ntMasks).all (fun p => masksOK 24 tT (toTable p.1) p.2)) &&
      (masksOK 24 tT qtT qtMasks) && ((kqT.zip kqMasks).all (fun p => masksOK 24 tT p.1 p.2)) &&
      ((cb0Gen.zip cb0Masks).all (fun p => masksOK 24 r2T (toTable p.1) p.2)) &&
      (ordTest 24 5 y5T) && (ordTest 24 7 y7T)) = true ∧
    ((sW.all fun w => lsChain.sift (tab (wordG gensG w)) 0) &&
      (etW.all fun w => lqChain.sift (tab (wordG gensG w)) 0) && (etT.all (CFSG.Sporadic.Schreier.Native.commAll 24 u5T)) &&
      (countProducts 24 (CFSG.Sporadic.Schreier.Native.commAll 24 u5T) (levelTables lqChain) (idT 24) == 64) &&
      (CFSG.Quasithin.KGC31.Native.blocksOK tets y5T) && (njT.all (CFSG.Quasithin.KGC31.Native.blocksOK tets)) && (sT.all (fixesBlocks tets)) &&
      (countProducts 24 (fixesBlocks tets) (levelTables lsChain) (idT 24) == 192)) = true ∧
    (!(inSpan 24 tT qtT) && (inSpan 24 tT (compT 24 qtT qtT)) && (CFSG.Sporadic.Th.Native.invOK 24 qtT (CFSG.Sporadic.Th.Native.invT 24 qtT)) &&
      (kqT.all fun k => CFSG.Sporadic.Th.Native.invOK 24 k (CFSG.Sporadic.Th.Native.invT 24 k) &&
        inSpan 24 tT (compT 24 (CFSG.Quasithin.KGC31.Native.conjTab 24 k (CFSG.Sporadic.Th.Native.invT 24 k) qtT) (CFSG.Sporadic.Th.Native.invT 24 qtT))) &&
      (cosetOK 24 b0T r2T r2CosetT) &&
      (cosetCount 24 cb0T r2CosetT (normAll 24 r2T) == 21504)) = true := KernelKGC31M24.cert7217

end Certificates
