module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

structure DataExt (D : Data G) : Prop where
  sig_nonempty : D.sig.Nonempty
  hne : (hSet D.T D.M).Nonempty
  three_le : ∀ p ∈ D.sig, 3 ≤ CFSG.Open.pRank p D.M
  four_le : 3 < CFSG.Open.evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M

theorem dataExt_ofSetup (hS : Standing G) (S : Setup G) : DataExt (PartTwo.Three.dataOfSetup hS S) where
  sig_nonempty := ⟨S.p, S.hp, S.P, S.witness⟩
  hne := S.hSet_nonempty
  three_le := fun q hq => by
    obtain ⟨hq1, Q, hw⟩ := hq
    exact ((hw.pRank_eq_three hS hq1).2).ge
  four_le := fun h => by
    exfalso
    rw [hS.rank] at h
    omega

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4) in
theorem dataExt_ofSetup4 (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) :
    DataExt (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) where
  sig_nonempty := ⟨S.p, S.hp⟩
  hne := S.hSet_nonempty
  three_le := fun p hp =>
    le_trans (by norm_num) (CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma hp)
  four_le := fun _ p hp => CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma hp

end CFSG.LocalAnalysis.UniquenessCase.UC22
