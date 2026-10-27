module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916.Defs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Omega
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

open CFSG CFSG.Open CFSG.RankThree.PartTwo.Sec19.Census194

theorem census1916SurvPSp_holds :
    Census1916SurvPSp := by
  intro Y _ _ n f hR hm hn
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    RonanC194.odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ :=
    CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hR.quasisimple hodd hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  have h3 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 f
    rw [one_pow] at h
    rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num]
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
    hn.trans (RonanC194.le_pRank_statedProj_sp (K := K) (n := n) Nat.prime_three (by rwa [hK]))
  exact hR.false_of_mulEquiv ((RonanC194.mulEquivQuotientCenterOfEqBot hZ).trans e).symm
    Nat.prime_three (by norm_num) h4

theorem census1916SurvPOmegaPlus_holds :
    Census1916SurvPOmegaPlus := by
  intro Y _ _ n f hR hm
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    RonanC194.odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ :=
    CFSG.SectionRank.EvenCover.even_split_orthogonal_odd_cover_catalog_step
      hR.quasisimple hodd hm
  obtain ⟨⟨-, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let eY : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) :=
    (RonanC194.mulEquivQuotientCenterOfEqBot hZ).trans e
  rcases Nat.eq_or_lt_of_le hf with rfl | hf2
  · exact hR.false_of_mulEquiv eY.symm Nat.prime_three (by norm_num)
      (RonanC194.OmegaEven.four_le_pRank_three_omegaPlus hn)
  · obtain ⟨r, hr, hr2, hrd⟩ := RonanC194.OmegaEven.exists_odd_prime_dvd_two_pow_sub_one hf2
    refine hR.false_of_mulEquiv eY.symm hr hr2 ?_
    exact hn.trans (RonanC194.OmegaEven.le_pRank_omegaPlus_torus hr hr2
      (by rw [Nat.card_units, hK]; exact hrd))

theorem census1916SurvPOmegaMinus_holds :
    Census1916SurvPOmegaMinus := by
  intro Y _ _ n f hR hm hn
  have hodd : Odd (Nat.card (Subgroup.center Y)) :=
    RonanC194.odd_card_center_of_pCore_eq_bot hR.pCore_two
  obtain ⟨hZ, -⟩ :=
    CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step
      hR.quasisimple hodd hm
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
  let eY : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) :=
    (RonanC194.mulEquivQuotientCenterOfEqBot hZ).trans e
  rcases Nat.eq_or_lt_of_le hf with rfl | hf2
  · exact hR.false_of_mulEquiv eY.symm Nat.prime_three (by norm_num)
      (RonanC194.OmegaEven.four_le_pRank_three_omegaMinus hn b c)
  · obtain ⟨r, hr, hr2, hrd⟩ := RonanC194.OmegaEven.exists_odd_prime_dvd_two_pow_sub_one hf2
    refine hR.false_of_mulEquiv eY.symm hr hr2 ?_
    exact (by omega : 4 ≤ n - 1).trans (RonanC194.OmegaEven.le_pRank_omegaMinus_torus hr hr2
      (by rw [Nat.card_units, hK]; exact hrd) b c)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916
