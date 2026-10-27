module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.LocalAnalysis.UniquenessCase.UC22S219Sig3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_isPowTwo_of_s21_9Sig3 {D : Data G} {Ch : Choice2011 G}
    (he : evenRank G = 3) (h1930 : H1930 D) (c : Ctx21 D Ch) (hH : Hyp2120 D c)
    (h219 : S21_9Sig3 D Ch) : ∀ L ∈ calC D.M, ∀ n, IsSU3 (Bar2 L) n → IsPowTwo n := by
  intro L hL n hU
  by_contra hnp
  obtain ⟨hN, hno⟩ := hH.2.1 L hL
  exact hno ⟨n, (h219 h1930 c L hL hN n hU hnp he).1, Or.inr hU⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
