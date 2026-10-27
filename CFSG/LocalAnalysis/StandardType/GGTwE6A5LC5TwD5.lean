module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A5LThreeCent
import CFSG.LocalAnalysis.StandardType.GGTwE6A5LThreeAdic
import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagLabels
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB


theorem ggTwE6A5LAt_symplectic_five {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hrank : lab.rank = 5) : GGTwE6A5LAt lab := by
  refine ggTwE6A5LAt_of_inner_not_marking_twA_five hlab ?_
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hrank ⊢
  subst hrank
  have hg : 1 ≤ g := hlab.1
  rcases htag with rfl | rfl
  all_goals
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hq⟩ := hQ
    have := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    refine ⟨K, inferInstance, inferInstance, hK, hq, ?_⟩
    intro hR hna hfin s n hsI hs3 hs1 h3n hgn J₁ hJ₁ hmark
    obtain ⟨x, rfl⟩ := matConjImage_gsp_subset_inn (K := K) 5 hsI
    have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_symplectic 5 g hK ⟨Nat.prime_two, hg, by norm_num, by simp⟩)).2.2.1
      rfl
    refine not_three_mul_ordTwistedA_five_dvd_ordBC_five hg hgn h3n ?_
    rw [← hcard]
    haveI := hfin
    exact three_mul_ordTwistedA_five_dvd_card_of_conj hR hna hs3 hs1 hJ₁.1 hmark

theorem ggTwE6A5LAt_twD_five {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twD) (hrank : lab.rank = 5) : GGTwE6A5LAt lab := by
  refine ggTwE6A5LAt_of_inner_not_marking_twA_five hlab ?_
  obtain ⟨t, l, g⟩ := lab
  dsimp only at htag hrank ⊢
  subst htag
  have hg : 1 ≤ g := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · exact absurd hrank (by omega)
  · exact absurd hrank (by omega)
  subst hrank
  obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, ?_⟩
  intro hR hna hfin s n hsI hs3 hs1 h3n hgn J₁ hJ₁ hmark
  obtain ⟨x, rfl⟩ := hsI
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_omegaMinus 5 g hK b c hbc ⟨Nat.prime_two, hg, by norm_num⟩)).2.2.2.2 rfl
  refine not_three_mul_ordTwistedA_five_dvd_ordTwistedD_five hg hgn h3n ?_
  rw [← hcard]
  haveI := hfin
  exact three_mul_ordTwistedA_five_dvd_card_of_conj hR hna hs3 hs1 hJ₁.1 hmark

end CFSG.StandardType.SCFourCover

end
