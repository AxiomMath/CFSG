module

public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2Inputs
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.OddCore.HeL2F

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native CFSG.Sporadic.HeldB in
open CFSG.Monster.B.Co2.Native in
theorem certificate2276 : ((∀ j < 9, permChk 42 (heInnerSigma1.getD j #[]) = true ∧
        (heInnerSigma1.getD j #[]).size = 42) ∧
      (∀ j < 6, ∀ i ∈ heRWords.getD j [], i < 9)
    )
    ∧ (enumOK 42 heRGens heREnum = true ∧ heREnum.tabs.size = 64 ∧
      normalOK 42 heREnum.tabs heXTabs heXInvs heRGens = true
    )
    ∧ (enumOK 42 heXTabs heXEnum = true ∧ heXEnum.tabs.size = 10752 ∧
      (heXEnum.tabs.toList.filter (commAll 42 heRGens)).length = 64
    ) := KernelSpor.He2276.facts2276

end Certificates
