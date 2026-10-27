module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3G

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M6_m3
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
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hm3 : MBarGT D.M V₀ V 2) :
    ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) := by
  have hsig_sub : ∀ q ∈ D.sig, q = 3 := by
    intro q hq
    rcases hres q hq with h | ⟨h7, -, -⟩
    · exact h.trans hp3
    · omega
  obtain ⟨q0, hq0⟩ := S.hx.sig_nonempty
  have h3mem : 3 ∈ D.sig := (hsig_sub q0 hq0) ▸ hq0
  have h3 : D.sig = {3} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨h3mem, fun q hq => hsig_sub q hq⟩
  have hmle : E3.mParam (Mbar D.M V₀ V h.hyp151.isElemAbelian) ≤ 2 :=
    s16h_mParam_le_two_of_Z3_six_two D S hσ h hc (hp3 ▸ hLp) hm hs2 h3
  have hnot2 : ¬ MBarGT D.M V₀ V 2 := fun hm2 =>
    not_lt.2 hmle ((h.hyp151.hyp125.mBarGT_iff_lt_mBar 2).1 hm2)
  exact (hnot2 hm3).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
