module

public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def Ce15Four (T Mc M : Subgroup G) : Prop :=
  Case1517Four T M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def Ce15Six (T Mc M : Subgroup G) (p : ℕ) : Prop :=
  Case1517Six T M (V154 T Mc M) (mBar0 T Mc M) p

@[expose] def Ce15Seven (T Mc M : Subgroup G) : Prop :=
  Case1517Seven T M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def Ce15ThreeCase (T Mc M : Subgroup G) : Prop :=
  Case1517Three M (V154 T Mc M) (mBar0 T Mc M)

@[expose] def Ce15 (T Mc M : Subgroup G) : Prop :=
  Ce15Four T Mc M ∨ (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ Ce15Six T Mc M p) ∨ Ce15Seven T Mc M

@[expose] def Ce15Small (T Mc M : Subgroup G) : Prop :=
  Ce15Four T Mc M ∨ Ce15Six T Mc M 3 ∨ Ce15Seven T Mc M

theorem Ce15Small.ce15 {T Mc M : Subgroup G} (h : Ce15Small T Mc M) : Ce15 T Mc M := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨3, Or.inl rfl, h⟩)
  · exact Or.inr (Or.inr h)

theorem Ce15.not_case3b {T Mc M : Subgroup G} (h : Ce15 T Mc M) : ¬ Case3bOf T Mc M :=
  fun hB => hB.2.2 h

@[expose] def StageTheorem1515 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → IsCE1513 T M → ¬ Ce15 T Mc M

theorem lemma1517_cases_of_theorem1515 (h : StageTheorem1515) {T Mc M : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (h157 : Lemma1517Concl T Mc M) :
    Case1517One M (V154 T Mc M) (mBar0 T Mc M) ∨ Case1517Two M (V154 T Mc M) (mBar0 T Mc M) ∨
      Case1517Three M (V154 T Mc M) (mBar0 T Mc M) ∨
      Case1517Five T M (V154 T Mc M) (mBar0 T Mc M) := by
  have hn := h G T Mc M hq hM hCE
  obtain ⟨hcases, -⟩ := h157
  rcases hcases with h1 | h2 | h3 | h4 | h5 | ⟨p, hp, h6⟩ | h7
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact (hn (Or.inl h4)).elim
  · exact Or.inr (Or.inr (Or.inr h5))
  · exact (hn (Or.inr (Or.inl ⟨p, hp, h6⟩))).elim
  · exact (hn (Or.inr (Or.inr h7))).elim

end CFSG.Quasithin
