module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Certificate14958

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint

theorem th_fus_check :
    fusCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thFusN thFusProg thFus =
      true :=
  Certificates.certificate14958

theorem fusionGenerationOf_Th :
    FusionGenerationOf NativeSporadic.Th 7 :=
  fusionGenerationOf_of_check (spec2 248) (D := thFus) (by show Nat.Prime 7; norm_num) th_fus_check

end CFSG.RankThree.PartOne.CTP
