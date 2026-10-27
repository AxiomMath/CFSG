module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_e3_CycTwoP7M6A_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

theorem s16h_e3_CycTwoP7M6_bad
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
    Case164_4 D V₀ V hV L := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsig : D.sig = {7} :=
    s16h_e3_CycTwoP7M6A_sig_eq D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm hbad
  have h7 : 7 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 7
  have hsc := s16h_e3_CycTwoP7M6A_pCoreOf_selfCentralizing D S hr3 hσ hV h hc hp hLp hχ hs2
    hres hp7 hm hbad
  have hfstar : IsElemAbelianOfRank 7 3 ↥(fstarBar D.M V₀ V hV) := by
    rw [fstarBar, s16h_e3_CycTwoP7M6A_fstar_eq_pCoreOf hsc]
    exact s16h_e3_CycTwoP7M6A_pCoreOf_elemAbelian D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7
      hm hbad
  refine ⟨7, Or.inr rfl, hp7 ▸ hLp, ?_, hsig, s16h_pRank_eq_three D S hr3 h7, hfstar⟩
  · rw [hm, s16h_e3_CycTwoP7M6A_dParam_seven]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
