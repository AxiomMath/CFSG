module

public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.RankThree.PartTwo.Sec19.Census194.Arith
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
public import CFSG.RankThree.PartOne.S12.ModelTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19
open CFSG.Open (StatedSp StatedProj)

theorem center_eq_bot_of_psp
    {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (hR : Census194RankHyp Y)
    (hm : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n 2 f) :
    Subgroup.center Y = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  haveI : Group.IsPerfect Y := hR.quasisimple.1
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic
    (odd_card_center_of_pCore_eq_bot hR.pCore_two) e

theorem survPSp_holds :
    Census194SurvPSp := by
  intro Y _ _ n f hR hm hn
  by_contra hcon
  have hZ := center_eq_bot_of_psp hR hm
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have hf : 1 ≤ f := hadm.2.1
  let eY : Y ≃* StatedProj (StatedSp n K) := (mulEquivQuotientCenterOfEqBot hZ).trans e
  have hTB : TooBig (StatedProj (StatedSp n K)) := by
    rcases Nat.lt_or_ge n 4 with h4 | h4
    · have hn3 : n = 3 := by omega
      have hf2 : 2 ≤ f := by
        by_contra h
        exact hcon ⟨hn3, by omega⟩
      obtain ⟨r, hr, hr3, hrd⟩ := exists_prime_gt_three_dvd_sq_sub_one hf2
      refine tooBig_of_prime hr hr3 ?_
      have := le_pRank_statedProj_sp (K := K) (n := n) hr (by rwa [hK])
      omega
    · refine tooBig_of_three ?_
      have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
        have h := Nat.sub_dvd_pow_sub_pow 4 1 f
        rw [one_pow] at h
        rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
      have := le_pRank_statedProj_sp (K := K) (n := n) Nat.prime_three (by rwa [hK])
      omega
  exact hR.false_of_tooBig (hTB.of_mulEquiv eY.symm)

theorem idPSp_holds :
    Census194IdPSp := by
  intro Y _ _ n f hR hm hn
  have hZ := center_eq_bot_of_psp hR hm
  have hf : 1 ≤ f := hm.1.2.1
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSp_of_statedClassicalModel hm
  have eY := (mulEquivQuotientCenterOfEqBot hZ).trans e
  rcases hn with rfl | ⟨rfl, rfl⟩
  · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inl ⟨eY⟩))⟩
  · iterate 8 right
    left
    exact ⟨eY⟩

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
