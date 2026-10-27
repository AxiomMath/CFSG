module

public import CFSG.RankThree.Native.ONSevenArrays
import Certificates.Kernel.ONSeven.RFactsQ
import Certificates.Kernel.ONSeven.RFactsC0
import Certificates.Kernel.ONSeven.RFactsC1
import Certificates.Kernel.ONSeven.RFactsC2
import Certificates.Kernel.ONSeven.RFactsC34

public section

namespace Certificates

open CertificateChecks.KernelSpor.ONR in
open CFSG CFSG.RankThree CFSG.RankThree.Native in
theorem certificate8133 : (onSevenQCheck onSevenQR onSevenQTabs onSevenLineTabs onSevenQCert = true)
    ∧ (
 onSevenCCheck (onSevenCR 0) (onSevenRepArr 0) (onSevenCArrs 0)
    (onSevenCTabs 0) (onSevenCCert 0) 1372 = true
)
    ∧ (
 onSevenCCheck (onSevenCR 1) (onSevenRepArr 1) (onSevenCArrs 1)
    (onSevenCTabs 1) (onSevenCCert 1) 1372 = true
)
    ∧ (
 onSevenCCheck (onSevenCR 2) (onSevenRepArr 2) (onSevenCArrs 2)
    (onSevenCTabs 2) (onSevenCCert 2) 1372 = true
)
    ∧ (
 onSevenCCheck (onSevenCR 3) (onSevenRepArr 3) (onSevenCArrs 3)
    (onSevenCTabs 3) (onSevenCCert 3) 49 = true
)
    ∧ (
 onSevenCCheck (onSevenCR 4) (onSevenRepArr 4) (onSevenCArrs 4)
    (onSevenCTabs 4) (onSevenCCert 4) 49 = true
)
    ∧ (
 onSevenFCheck (onSevenCR 0) (onSevenCTabs 0) (onSevenCCert 0)
    (onSevenFArrs 0) (onSevenFTabs 0) (onSevenRepTab 0) (onSevenFCert 0) = true
)
    ∧ (
 onSevenFCheck (onSevenCR 1) (onSevenCTabs 1) (onSevenCCert 1)
    (onSevenFArrs 1) (onSevenFTabs 1) (onSevenRepTab 1) (onSevenFCert 1) = true
)
    ∧ (
 onSevenFCheck (onSevenCR 2) (onSevenCTabs 2) (onSevenCCert 2)
    (onSevenFArrs 2) (onSevenFTabs 2) (onSevenRepTab 2) (onSevenFCert 2) = true
) :=
  ⟨q_check, c_check0, c_check1, c_check2, c_check3, c_check4, f_check0, f_check1, f_check2⟩

end Certificates
