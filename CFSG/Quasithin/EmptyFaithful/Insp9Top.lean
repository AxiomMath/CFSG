module

public import CFSG.Quasithin.EmptyFaithful.Insp9Basic
public import CFSG.Quasithin.EmptyFaithful.Insp9Case

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Insp9

@[expose] def InspCase (P : ∀ {D : Type} [Group D], Subgroup D → Subgroup D → Prop) : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (D₁ D₂ J N : Subgroup D), Data D₁ D₂ J N →
    B56Setting D N → (P D₁ D₂ ∨ P D₂ D₁) → InspGoal D N

theorem inspectListF618_of_cases
    (h1 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseOne H₁ H₂)
    (h2 : InspCase fun {D} _ _ _ => F6.IsF618CaseTwo D)
    (h3 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseThree H₁ H₂)
    (h4 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseFour H₁ H₂)
    (h5 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseFive H₁ H₂)
    (h6 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseSix H₁ H₂)
    (h7 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseSeven H₁ H₂)
    (h8 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseEightCat H₁ H₂)
    (h9 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseNineCat H₁ H₂)
    (h10 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseTen H₁ H₂)
    (h11 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseEleven H₁ H₂)
    (h12 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseTwelve H₁ H₂)
    (h13 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseThirteen H₁ H₂) : InspectListF618 := by
  intro D _ _ D₁ D₂ J N hA hF hJ1 hJ2 hJN hcomm hN W _ _ hW ρ hρ hB53 hcases
  have hdata : Data D₁ D₂ J N := ⟨hA, hJ1, hJ2, hJN, hcomm, hN⟩
  have hs : B56Setting D N := ⟨W, inferInstance, inferInstance, hW, ρ, hρ, hB53, hcases⟩
  have key : (F6.IsF618CaseOrientedCat D₁ D₂ ∨ F6.IsF618CaseOrientedCat D₂ D₁) → InspGoal D N := by
    intro hO
    rcases hO with hO | hO
    · rcases hO with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
      · exact h1 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h2 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h3 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h4 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h5 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h6 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h7 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h8 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h9 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h10 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h11 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h12 D D₁ D₂ J N hdata hs (Or.inl hc)
      · exact h13 D D₁ D₂ J N hdata hs (Or.inl hc)
    · rcases hO with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
      · exact h1 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h2 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h3 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h4 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h5 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h6 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h7 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h8 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h9 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h10 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h11 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h12 D D₁ D₂ J N hdata hs (Or.inr hc)
      · exact h13 D D₁ D₂ J N hdata hs (Or.inr hc)
  exact key hF

end Insp9

end CFSG.Quasithin
