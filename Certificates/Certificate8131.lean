module

public import CFSG.RankThree.Native.LyFiveImagesInputs
import Certificates.Kernel.SporSch.Ly.Five8131

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native in
theorem certificate8131 : lyFiveTbArr.toList.Nodup := KernelSporSch.LyFT.nodup

end Certificates
