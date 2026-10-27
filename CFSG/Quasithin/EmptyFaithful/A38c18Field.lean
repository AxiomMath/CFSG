module

public import CFSG.Quasithin.EmptyFaithful.A38c12FieldOne

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.GoldS146R

namespace A38c18

@[expose] def StageTheorem1427Field : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M →
    (∀ H₂ K₂ : Subgroup G, IsHStar T M H₂ → ¬ Group.IsSolvable ↥H₂ → K₂ ∈ cComp H₂ →
        H₂ = K₂ ⊔ T → E2.E22CasesNoN H₂ T (H₂ ⊓ M) K₂ →
        ∀ n : ℕ, A38c12.E22Field H₂ T (H₂ ⊓ M) K₂ n → n = 1) ∨
      (Nonempty (G ≃* quasithinTrialityD4Two) ∨ Nonempty (G ≃* quasithinJ2) ∨
        Nonempty (G ≃* quasithinJ3))

theorem fieldOne146_of_stageTheorem1427Field (h : StageTheorem1427Field) :
    A38c12.FieldOne146 := by
  intro G _ _ T M S H₂ K₂ hStar hns hK₂ hHK₂ hcases n hn
  rcases h G T M S.hyp with h | h
  · exact h H₂ K₂ hStar hns hK₂ hHK₂ hcases n hn
  · exfalso
    apply S.notSix
    rcases h with h | h | h
    · exact (sixModels_iff G).mpr (Or.inr (Or.inr (Or.inl h)))
    · exact (sixModels_iff G).mpr (Or.inl h)
    · exact (sixModels_iff G).mpr (Or.inr (Or.inl h))

end A38c18

end CFSG.Quasithin
