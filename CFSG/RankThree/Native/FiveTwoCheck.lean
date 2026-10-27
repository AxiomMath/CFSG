module

public import CFSG.RankThree.Native.FiveTwoData
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public meta import CFSG.RankThree.Native.FiveTwoData
public meta import Certificates.Data.CFSGNative.SectionRank.F2
public meta import Certificates.Data.CFSGNative.SectionRank.F3
public meta import Certificates.Data.CFSGNative.SectionRank.Fp
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8127
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.Native

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem j3FiveTwo_check :
    FiveTwoData.check (ops2 80) j3FiveTwo = true :=
  Certificates.certificate8127.1

theorem co1FiveTwo_check :
    FiveTwoData.check (ops2 24) co1FiveTwo = true :=
  Certificates.certificate8127.2.1

theorem co2FiveTwo_check :
    FiveTwoData.check (ops2 22) co2FiveTwo = true :=
  Certificates.certificate8127.2.2.1

theorem co3FiveTwo_check :
    FiveTwoData.check (ops2 22) co3FiveTwo = true :=
  Certificates.certificate8127.2.2.2.1

theorem hsFiveTwo_check :
    FiveTwoData.check (ops2 20) hsFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.1

theorem mclFiveTwo_check :
    FiveTwoData.check (ops3 21) mclFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.1

theorem hnFiveTwo_check :
    FiveTwoData.check (opsP 5 133) hnFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.2.1

theorem suzFiveTwo_check :
    FiveTwoData.check (ops3 64) suzFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.2.2.1

theorem lyFiveTwo_check :
    FiveTwoData.check (opsP 5 111) lyFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.2.2.2.1

theorem thFiveTwo_check :
    FiveTwoData.check (ops2 248) thFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.2.2.2.2.1

theorem onFiveTwo_check :
    FiveTwoData.check (ops3 154) onFiveTwo = true :=
  Certificates.certificate8127.2.2.2.2.2.2.2.2.2.2

theorem j3_commuting_two_five :
    ∃ z y : NativeSporadic.J3, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 80) j3FiveTwo j3FiveTwo_check

theorem co1_commuting_two_five :
    ∃ z y : NativeSporadic.Co1, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 24) co1FiveTwo co1FiveTwo_check

theorem co2_commuting_two_five :
    ∃ z y : NativeSporadic.Co2, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 22) co2FiveTwo co2FiveTwo_check

theorem co3_commuting_two_five :
    ∃ z y : NativeSporadic.Co3, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 22) co3FiveTwo co3FiveTwo_check

theorem hs_commuting_two_five :
    ∃ z y : NativeSporadic.HS, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 20) hsFiveTwo hsFiveTwo_check

theorem mcl_commuting_two_five :
    ∃ z y : NativeSporadic.McL, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec3 21) mclFiveTwo mclFiveTwo_check

theorem hn_commuting_two_five :
    ∃ z y : NativeSporadic.HN, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (specP 5 133) hnFiveTwo hnFiveTwo_check

theorem suz_commuting_two_five :
    ∃ z y : NativeSporadic.Suz, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec3 64) suzFiveTwo suzFiveTwo_check

theorem ly_commuting_two_five :
    ∃ z y : NativeSporadic.Ly, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (specP 5 111) lyFiveTwo lyFiveTwo_check

theorem th_commuting_two_five :
    ∃ z y : NativeSporadic.Th, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec2 248) thFiveTwo thFiveTwo_check

theorem on_commuting_two_five :
    ∃ z y : NativeSporadic.ON, orderOf z = 2 ∧ orderOf y = 5 ∧ z * y = y * z :=
  OpsSpec.exists_of_fiveTwoCheck (spec3 154) onFiveTwo onFiveTwo_check

end CFSG.RankThree.Native
