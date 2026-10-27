module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M6A1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M6A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_cyclic_two_p3m6
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 6) :
    ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  by_cases hm2 : MBarGT D.M V₀ V 2
  · exact s16h_e3_CycTwoP3M6_m3 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hm2
  · exact s16h_e3_CycTwoP3M6_m2 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hm2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
