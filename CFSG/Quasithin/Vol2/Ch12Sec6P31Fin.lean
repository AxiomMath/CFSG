module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31e
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Claim

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

theorem lemma12_6_31_of (hLie : L34LieFacts12631) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h1229 : Lemma12_6_29) (h1230 : Lemma12_6_30) (hK : KList12631) : Lemma12_6_31 := by
  intro G _ _ T L V _ F hH hZ H K hIs
  have h918 : HypF918 T V L F.V1 F.V5 H K := ((h1230 G T L V F hH hZ).2 H K hIs).2.2
  rcases hK G T L V F hH hZ H K hIs with hA | ⟨hK₀, hL⟩
  · by_cases hK₀ : conjClosure K T = K
    · exact Or.inr (Or.inr (S126P31.case3_of h1222 h1228 h1229 F hH hZ hIs h918 hA hK₀))
    · exact Or.inr (Or.inl (S126P31.case2_of h1222 h1229 F hH hZ hIs h918 hA hK₀))
  · exact Or.inl (S126P31.case1_of hLie h1222 h1228 h1229 F hH hZ hIs h918 hK₀ hL)

end CFSG.Quasithin.H13
