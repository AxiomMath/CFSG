module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M4AA2AAA_sigma_eq_three
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
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    D.sig = {3} ∧ CFSG.Open.pRank 3 D.M = 3 := by
  have hsub : ∀ q ∈ D.sig, q = 3 := by
    intro q hq
    rcases hres q hq with hq3 | ⟨h7, -, -⟩
    · exact hq3.trans hp3
    · exact absurd (hp3 ▸ h7) (by norm_num)
  obtain ⟨q₀, hq₀⟩ := S.hx.sig_nonempty
  have hsig : D.sig = {3} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨(hsub q₀ hq₀) ▸ hq₀, fun q hq => hsub q hq⟩
  have h3mem : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  exact ⟨hsig, s16h_pRank_eq_three D S hr3 h3mem⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
