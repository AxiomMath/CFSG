module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapInspBC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c167_exists_choice1613 (D : Data G) (h61 : UC6.R6_1 D) (hBC : S16GapInspBC D)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    (h12 : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M) :
    ∃ A : Subgroup G, Choice1613 D ⊥ V hV L A := by
  by_contra hne
  have hh := hc.setting.hyp16.hyp125
  have hcomm_each : ∀ A ∈ E3.gammaSet V D.k D.T,
      ⁅oddBar D.M ⊥ V hV, barSub ⊥ V hV A⁆ = ⊥ := by
    intro A hA
    by_contra hA1
    exact hne ⟨A, by unfold Choice1613; exact ⟨hA, Or.inl hA1⟩⟩
  have h9 : Case168_9 D ⊥ V hV L → ∀ A ∈ E3.gammaSet V D.k D.T,
      barSub ⊥ V hV A ≤ stabSub (wTil ⊥ V hV L) := by
    intro h9 A hA
    by_contra hA2
    exact hne ⟨A, by unfold Choice1613; exact ⟨hA, Or.inr ⟨h9, hA2⟩⟩⟩
  have hcomm := s16c167_comm_wClos_of_forall hh hcomm_each
  have hU : Insp1613U D V := by
    by_cases hnc : OddNcCore D ⊥ V hV
    · exact s16c167_insp1613U_of_oddNc D hh hnc hcomm
    · exact hBC V L hV hc hnc hcomm h9
  exact s16c167_false_of_insp1613U D h61 (B2F.isPGroup_of_isElemAbelian hV)
    (s15_13A_le_T hh) h12 hU

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
