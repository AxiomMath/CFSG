module

public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2Inputs
public import Certificates.Certificate2276

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

theorem he2_basic :
    (∀ j < 9, permChk 42 (heInnerSigma1.getD j #[]) = true ∧
      (heInnerSigma1.getD j #[]).size = 42) ∧
    (∀ j < 6, ∀ i ∈ heRWords.getD j [], i < 9) :=
  Certificates.certificate2276.1

theorem he2_R :
    enumOK 42 heRGens heREnum = true ∧ heREnum.tabs.size = 64 ∧
      normalOK 42 heREnum.tabs heXTabs heXInvs heRGens = true :=
  Certificates.certificate2276.2.1

theorem he2_X :
    enumOK 42 heXTabs heXEnum = true ∧ heXEnum.tabs.size = 10752 ∧
      (heXEnum.tabs.toList.filter (commAll 42 heRGens)).length = 64 :=
  Certificates.certificate2276.2.2

end CFSG.Sporadic.SmallOddCore
