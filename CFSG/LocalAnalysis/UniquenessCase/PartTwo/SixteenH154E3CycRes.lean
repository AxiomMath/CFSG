module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycS3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycThreeThird

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_cyclic_two_resid
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hrow : s16h_ZpRow p (rk ↥(wTil V₀ V h.hyp151.isElemAbelian L)))
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n)
    (hs2 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6 ∧ q = 3)) :
    Hyp154 D V₀ V L ∨ Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  have hδ2 := hδ hs2
  have hp2 : p ≠ 2 := by
    rcases hrow with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hfin : (∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) → Hyp154 D V₀ V L := fun hW1 =>
    s16h_hyp154_of_unique₁_two D h.hyp151 hs2 (s16h_unique₁_of_wSub D h.hyp151 hv1 hW1) hδ2
  have hc4 : Case164_4 D V₀ V hV L → Concl164 D V₀ V hV L := fun hC =>
    ⟨hs2, Or.inr (Or.inr (Or.inr hC))⟩
  by_cases hm3 : rk ↥(wTil V₀ V hV L) ≤ 3
  · exact Or.inr (s16h_e3_cyclic_two_small D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp2 hm3)
  · unfold s16h_ZpRow at hrow
    rcases hrow with ⟨hp3, hm⟩ | ⟨hp5, hm⟩ | ⟨hp7, hm⟩
    · rcases hm with hm | hm | hm
      · exact absurd (by omega) hm3
      · rcases s16h_e3_cyclic_two_p3m4 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm with hW | hC
        · exact Or.inl (hfin hW)
        · exact Or.inr (hc4 hC)
      · exact Or.inl (hfin (s16h_e3_cyclic_two_p3m6 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm))
    · exact Or.inl (hfin (s16h_e3_cyclic_two_p5 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp5 hm))
    · rcases hm with hm | hm
      · exact absurd (by omega) hm3
      · rcases s16h_e3_cyclic_two_p7m6 D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm with hW | hC
        · exact Or.inl (hfin hW)
        · exact Or.inr (hc4 hC)

theorem s16h_e3_cyclic_three_resid
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V h.hyp151.isElemAbelian,
      n ∈ normalizer ((lBar V₀ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V h.hyp151.isElemAbelian L, n * l = l * n)
    (hs3 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 3)
    (hv1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≤ V₀)
    (hpσ : p ∉ D.sig) (h3 : D.sig = {3})
    (hn76 : ¬ (p = 7 ∧ rk ↥(wTil V₀ V h.hyp151.isElemAbelian L) = 6)) :
    Hyp154 D V₀ V L ∨ Concl164 D V₀ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨h1, h2⟩ := s16h_e3_cyclic_unique_of_s_ge_three D S hσ h hc hp hLp (by omega) hχ
  have hcent := s16h_e3_cyclic_three_cent D S hr3 hσ hV h hc hp hLp hχ hs3 hpσ h3 hn76
  have hthird := s16h_e3_cyclic_third_three D S hσ hV h h3 hv1 h1 hcent
  exact Or.inl ⟨h.hyp151, h1, h2, fun g hg X hX Y hY hXY hne =>
    absurd (hthird g hg X hX Y hY hXY) hne⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
