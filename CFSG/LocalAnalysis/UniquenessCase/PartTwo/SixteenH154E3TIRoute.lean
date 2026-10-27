module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_uniqueMax_of_le' {M E C : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hEC : E ≤ C) (hCM : C ≤ M) (hE : UniqueMax M E) : UniqueMax M C := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hM, hCM⟩, fun N hN => ?_⟩
  have hN' : N ∈ calMOf E := ⟨hN.1, hEC.trans hN.2⟩
  rw [hE] at hN'
  exact hN'

theorem s16h_e3_ti_V1_false (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    {V₁ : Subgroup G} (hV : InCalV D.M V₁)
    (hw : ∀ w ∈ V₁, w ≠ 1 → ∃ p ∈ D.sig,
      2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({w} : Set G)))
    {q : ℕ} (hq : q ∈ D.sig) {E : Subgroup G}
    (hEN : E ≤ D.M ⊓ normalizer ((D.T ⊓ centralizer (V₁ : Set G) : Subgroup G) : Set G))
    (hEq : IsPGroup q E) (hEc : ¬ IsCyclic E) (h8 : 8 ≤ Nat.card V₁) : False := by
  have hTI : CFSG.CGT.Timmesfeld75.IsTI V₁ :=
    s16_TI_of_pRank D h61 hV.2.2.2 hV.2.2.1 hw
  have hU : UniqueMax D.M (D.M ⊓ normalizer
      ((D.T ⊓ centralizer (V₁ : Set G) : Subgroup G) : Set G)) :=
    s16h_e3_uniqueMax_of_le' D.maxLocal hEN inf_le_left
      (h61 q hq E (hEN.trans inf_le_left) hEq hEc)
  exact (h127 h124 V₁ hV hTI h8).1 ⟨hV, hU⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
