module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA3A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA3B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_sig_eq
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
    (hp7 : p = 7) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hbad : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    D.sig = {7} := by
  have h3 : 3 ∉ D.sig := by
    intro h3mem
    have h2 := s16h_e3_CycTwoP7M6A_rank_two_of_bad D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm
      hbad 3 h3mem
    have h1 := s16h_e3_CycTwoP7M6A_pRank_three_le_one D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7
      hm hbad
    omega
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    rcases hres q hq with h | ⟨-, -, h3q⟩
    · exact (h.trans hp7) ▸ hq
    · exact (h3 (h3q ▸ hq)).elim
  · intro q hq
    rcases hres q hq with h | ⟨-, -, h3q⟩
    · exact h.trans hp7
    · exact (h3 (h3q ▸ hq)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
