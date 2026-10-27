module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2121e_isPowTwo_of_s21_9N {D : Data G} {Ch : Choice2011 G} (h1930 : H1930 D)
    (c : Ctx21 D Ch) (hH : Hyp2120 D c) (h219 : S21_9N D Ch) (he : CFSG.Open.evenRank G ≠ 3) :
    ∀ L ∈ calC D.M, ∀ n, IsSU3 (Bar2 L) n → IsPowTwo n :=
  fun L hL n hU => by_contra fun hnp => he (h219 h1930 c L hL (hH.2.1 L hL).1 n hU hnp)

theorem uc22p2121e_types_of_isPowTwo {D : Data G} {Ch : Choice2011 G} (h1930 : H1930 D)
    (c : Ctx21 D Ch) (hH : Hyp2120 D c) (h216 : S21_16 D Ch)
    (hpow : ∀ L ∈ calC D.M, ∀ n, IsSU3 (Bar2 L) n → IsPowTwo n) {L : Subgroup G}
    (hL : L ∈ calC D.M) :
    (∃ n, IsL2 (Bar2 L) n) ∨ (∃ n, IsSz (Bar2 L) n) ∨ (∃ k, 1 ≤ k ∧ IsSU3 (Bar2 L) (2 ^ k)) ∨
      (∃ q, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 L) q) ∨ IsJ1 (Bar2 L) := by
  obtain ⟨-, hno⟩ := hH.2.1 L hL
  rcases h216 h1930 c L hL with ⟨n, hn, hSp⟩ | ⟨n, hU⟩ | hL2 | hSz | hOdd | hJ
  · exact absurd ⟨n, hn, Or.inl hSp⟩ hno
  · obtain ⟨k, rfl⟩ := hpow L hL n hU
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd ⟨2 ^ 0, by norm_num, Or.inr hU⟩ hno
    · exact Or.inr (Or.inr (Or.inl ⟨k, hk, hU⟩))
  · exact Or.inl hL2
  · exact Or.inr (Or.inl hSz)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hOdd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hJ)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
