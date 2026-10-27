module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_2_1 {T Mc M : Subgroup G} (h157 : Lemma1517Concl T Mc M)
    (h1515 : ¬ (Case1517Four T M (V154 T Mc M) (mBar0 T Mc M) ∨
      (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p) ∨
      Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M))) :
    Lemma15201Concl T Mc M := by
  obtain ⟨hcases, hlt⟩ := h157
  rcases hcases with h | h | h | h | h | h | h
  · exact ⟨h.1, Or.inl h, hlt⟩
  · exact ⟨h.1, Or.inr (Or.inl h), hlt⟩
  · exact ⟨h.1, Or.inr (Or.inr (Or.inl h)), hlt⟩
  · exact absurd (Or.inl h) h1515
  · exact ⟨h.1, Or.inr (Or.inr (Or.inr h)), hlt⟩
  · exact absurd (Or.inr (Or.inl h)) h1515
  · exact absurd (Or.inr (Or.inr h)) h1515

theorem stageLemma15201_of (h157 : StageLemma1517) (h1515 : StageTheorem15115) :
    StageLemma15201 := by
  intro G _ _ T Mc M hs
  exact lemma_15_2_1 (h157 G T Mc M hs.qtfe hs.mf hs.ce) (h1515 G T Mc M hs.qtfe hs.mf hs.ce)

end CFSG.Quasithin
