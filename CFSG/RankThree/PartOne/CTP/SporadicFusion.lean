module

public import CFSG.RankThree.PartOne.CTP.FusionSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate14955
public import Certificates.Certificate14956

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint

theorem j2_fus_check :
    fusCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2 j2FusN j2FusProg j2Fus =
      true :=
  Certificates.certificate14955

theorem fusionGenerationOf_J2 :
    FusionGenerationOf NativeSporadic.J2 5 :=
  fusionGenerationOf_of_check (specP 5 14) (D := j2Fus) Nat.prime_five j2_fus_check

theorem he_fus_check :
    fusCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2 heFusN heFusProg heFus =
      true :=
  Certificates.certificate14956

theorem fusionGenerationOf_He :
    FusionGenerationOf NativeSporadic.He 5 :=
  fusionGenerationOf_of_check (specP 7 50) (D := heFus) Nat.prime_five he_fus_check

end CFSG.RankThree.PartOne.CTP
