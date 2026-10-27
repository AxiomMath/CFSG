module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem trichotomy_of_lt (D : Data G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hr : (D.k : ℕ∞) < E3.rParam V) (hβ : (D.k : ℕ∞) < betaN 0 D.M V) :
    ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M ∨
      ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M ∨ (calO2 D.k D.M V₀ V).Nonempty := by
  refine or_iff_not_imp_left.2 fun hN => or_iff_not_imp_left.2 fun hC => ?_
  rw [not_not] at hN hC
  obtain ⟨H, A, K, hS, hA, hK, hne⟩ := s15_Thirteen_exists_A_K D h126 h hN hC
  exact s15_Thirteen_six_nine D h hS hA hK hr hβ hne

theorem r16_24c_of_lt (D : Data G) (h126 : R126 D)
    (hlt : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      (Case167_3 D V₀ V hV L ∨ Case167_4 D V₀ V hV L ∨ Case167_7 D V₀ V hV L ∨
        Case167_8 D V₀ V hV L) →
      (D.k : ℕ∞) < E3.rParam V ∧ (D.k : ℕ∞) < betaN 0 D.M V) : R16_24c D := by
  intro V₀ V L hV hS hc
  obtain ⟨hr, hβ⟩ := hlt V₀ V L hV hS hc
  exact trichotomy_of_lt D h126 hS.setting.hyp16.hyp125 hr hβ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
