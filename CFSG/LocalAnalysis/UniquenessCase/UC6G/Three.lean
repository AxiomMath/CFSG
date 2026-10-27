module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Final
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

variable {G : Type} [Group G] [Finite G]

theorem hooks_dataOfSetup (hS : Standing G) (S : Setup G) : Hooks (PartTwo.Three.dataOfSetup hS S) where
  nonempty := (UC6S846.sigmaStd_dataOfSetup hS S).nonempty
  three_le := (UC6S846.sigmaStd_dataOfSetup hS S).three_le
  sig1_sp := (UC6S846.sigmaStd_dataOfSetup hS S).sig1_sp
  four_mem := (UC6S846.sigmaStd_dataOfSetup hS S).four_mem
  three_mem_sub := fun H h => by
    exfalso
    have h1 : CFSG.Open.twoLocalPrimeRank 3 ↥H ≤ evenRank ↥H :=
      CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank 3 Nat.prime_three (by norm_num)
    have h2 := CFSG.RankThree.PartTwo.evenRank_subgroup_le H
    rw [hS.rank] at h2
    omega
  three_mem_top := fun h => by
    exfalso
    have h1 : CFSG.Open.twoLocalPrimeRank 3 G ≤ evenRank G :=
      CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank 3 Nat.prime_three (by norm_num)
    rw [hS.rank] at h1
    omega

theorem theoremCAt_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G) :
    TheoremCAt (PartTwo.Three.dataOfSetup hS S).M :=
  hC hUC S.p S.hp S.P S.M S.witness

section


theorem uc_theorem_6_14_three
    (hS : Standing G) (hUC : rankThreeUC G) (hC : AGL81TheoremC G)
    (hK : UCK.K36) (S : Setup G) : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S) :=
  r6_14_of_hooks (hooks_dataOfSetup hS S) (theoremCAt_dataOfSetup hS hUC hC S)
    (PartTwo.Three.r6_7_dataOfSetup hS hUC hC hK S)

end

end CFSG.LocalAnalysis.UniquenessCase.UC6G
