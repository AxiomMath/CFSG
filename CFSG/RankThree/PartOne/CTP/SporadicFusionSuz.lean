module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate14957

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint

theorem suz_fus_check :
    fusCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 suzFusN suzFusProg suzFus =
      true :=
  Certificates.certificate14957

theorem fusionGenerationOf_Suz :
    FusionGenerationOf NativeSporadic.Suz 5 :=
  fusionGenerationOf_of_check (spec3 64) (D := suzFus) Nat.prime_five suz_fus_check

end CFSG.RankThree.PartOne.CTP
