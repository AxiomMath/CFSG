module

import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec15.Sylow155B1P

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Sylow155S

theorem sup_mem_invariant {A X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hE : End155N A X K Y M T P) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) :
    CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) ∈
      invariantPiSubgroups ⊤ A (piCompl 3) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU0 := Sylow155B1.pPrimeCoreOf_u155_mem_invariant hC
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hR3 : IsPiSubgroup (piCompl 3) (CFSG.Open.pCoreOf 2 Y) := by
    refine (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr fun h3 => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hRU0 : CFSG.Open.pCoreOf 2 Y ≤ Subgroup.normalizer (pPrimeCoreOf 3 (u155 A M X) : Set G) :=
    (Sylow155F.r_le_u155 hE hRP).trans (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_pPrimeCoreOf 3 _))
  exact ⟨le_top, isPiSubgroup_piCompl_sup hR3 hU0.2.1 hRU0,
    le_normalizer_sup (Sylow155B1.le_normalizer_r hC) hU0.2.2⟩

theorem sup_le_u155 {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P)
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P) :
    CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) ≤ u155 A M X :=
  sup_le (Sylow155F.r_le_u155 hE hRP) (pPrimeCoreOf_le 3 _)

theorem p_le_normalizer_sup {A X K Y M T P : Subgroup G} (hE : End155N A X K Y M T P) :
    P ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X) : Subgroup G) : Set G) :=
  le_normalizer_sup (le_sup_left.trans (Sylow155F.sup_le_normalizer_r hE))
    (Sylow155B1.p_le_normalizer_of_host hE (normalizer_le_normalizer_pPrimeCoreOf 3 _))

end Sylow155S

end CFSG.RankThree.PartTwo.Sec15
