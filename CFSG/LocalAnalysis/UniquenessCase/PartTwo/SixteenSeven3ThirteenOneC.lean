module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapAEmpty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3GapM

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c167_case168_2_of_le_conj (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h111 : W3Thm111 G) (hAE : S16GapAEmpty D) (hM : S16GapMGtOne D)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    (h13b : Concl1613_2 D ⊥ V hV L) {g : G} (hVM : V ≤ conjSubgroup D.M g)
    (hVg : ¬ conjSubgroup V g ≤ D.M) : Case168_2 D ⊥ V hV L := by
  by_contra hn
  have hm : 1 < mBar D.M ⊥ V hV := hM V L hV hc
  have hother : Case168_3 D ⊥ V hV L ∨ (∃ r : ℕ, 3 ≤ r ∧ Case168_4With D ⊥ V hV L r) ∨
      Case168_8 D ⊥ V hV ∨ Case168_9 D ⊥ V hV L ∨ Case168_10 D ⊥ V hV L ∨
      Case168_11 D ⊥ V hV L := by
    rcases h13b with h | h | h | h | h | h | h
    · exact absurd (Case168_2Small.case168_2 D ⊥ V hV L h) hn
    · exact Or.inr (Or.inl ⟨3, le_rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hempty := hAE V L hV hc hother
  have hne := s16c167_calABar_nonempty_of_le_conj D hx h61 h111 hc.setting.hyp16 hm hVM hVg
  exact (Set.not_nonempty_iff_eq_empty.2 hempty) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
