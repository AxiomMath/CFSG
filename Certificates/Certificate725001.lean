module

public import Certificates.Data.Insp443M24
import Certificates.Kernel.Insp443M24.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Certificates
  CFSG.SectionRank.QTK.Insp443.M24 in
theorem certificate725001 :
    (CFSG.Sporadic.Th.Native.invOK 24 gT (CFSG.Sporadic.Th.Native.invT 24 gT) && (CFSG.Quasithin.KGC31.M24.conjAll gT tT).all (inSpan 24 etT)) = true ∧
    (CFSG.Sporadic.Th.Native.invOK 24 zT (CFSG.Sporadic.Th.Native.invT 24 zT) && CFSG.Sporadic.Th.Native.invOK 24 CFSG.SectionRank.QTK.Insp443.M24.lT (CFSG.Sporadic.Th.Native.invT 24 CFSG.SectionRank.QTK.Insp443.M24.lT) &&
      lqChain.sift (tab (wordG gensG lW)) 0 && ebasisOK 24 sixT &&
      sixT.all (inSpan 24 etT)) = true ∧
    (ordTest 24 7 CFSG.SectionRank.QTK.Insp443.M24.xT && CFSG.Sporadic.Schreier.Native.commT 24 b0T CFSG.SectionRank.QTK.Insp443.M24.xT && cjT.all (CFSG.Sporadic.Schreier.Native.commT 24 b0T) && cbChain.check &&
      (cbChain.orderCertificate == 21504)) = true ∧
    (CFSG.Sporadic.Th.Native.invOK 24 nT (CFSG.Sporadic.Th.Native.invT 24 nT) && masksOK 24 etT nT nMasks &&
      (lqGen.all fun g => CFSG.Sporadic.Th.Native.invOK 24 (toTable g) (CFSG.Sporadic.Th.Native.invT 24 (toTable g)) &&
        inSpan 24 etT
          (compT 24 (CFSG.Quasithin.KGC31.Native.conjTab 24 (toTable g) (CFSG.Sporadic.Th.Native.invT 24 (toTable g)) nT) (CFSG.Sporadic.Th.Native.invT 24 nT))) &&
      ebasisOK 24 (u5T ++ CFSG.Quasithin.KGC31.M24.conjAll nT u5T) && u5T.all (inSpan 24 etT) &&
      ((nqGen.zip nqEtMasks).all fun p => masksOK 24 etT (toTable p.1) p.2) &&
      masksOK 24 etT y7T y7EtMasks &&
      ((mjT.zip mjEtMasks).all fun p => masksOK 24 etT p.1 p.2)) = true := KernelInsp443M24.cert725001

end Certificates
