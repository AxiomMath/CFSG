module

public import CFSG.Sporadic.Bridge.BTc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThThreeTc
public import CFSG.Sporadic.Bridge.BData
public import CFSG.Monster.B.Pinned.Primes.Program
public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BCoxeterRels
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import Certificates.Certificate9650
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.RankThree.PartOne.CTP.Fus CFSG.Monster.B CFSG.Monster.B.Pinned

local notation "uT" => qFive 1 * qFive 2 ^ 2 * qFive 3 * zFive ^ 4

theorem fusionGenerationOf_B_five :
    FusionGenerationOf NativeSporadic.B 5 := by
  have : Nontrivial NativeSporadic.B :=
    ⟨⟨xFive, 1, fun h => xFive_not_mem (h ▸ QFive.one_mem)⟩⟩
  exact CFSG.AGLEmbedding.R3.fusionGenerationOf_of_tc Nat.prime_five tcGenDatum_B_five

end CFSG.Sporadic.Bridge.B
