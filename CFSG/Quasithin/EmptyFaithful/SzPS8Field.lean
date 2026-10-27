module

public import CFSG.Quasithin.EmptyFaithful.A38c18Field
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SzPS8

@[expose] def FieldOne1432 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ∀ H₂ K₂ : Subgroup G, IsHStar T M H₂ → ¬ Group.IsSolvable ↥H₂ → K₂ ∈ cComp H₂ →
      H₂ = K₂ ⊔ T → E2.E22CasesNoN H₂ T (H₂ ⊓ M) K₂ →
        ∀ n : ℕ, A38c12.E22Field H₂ T (H₂ ⊓ M) K₂ n → n = 1

theorem fieldOne1432_of_field (h : A38c18.StageTheorem1427Field) : FieldOne1432 := by
  intro G _ _ T M hyp hnot H₂ K₂ hStar hns hK₂ hHK₂ hcases n hn
  rcases h G T M hyp with h | h
  · exact h H₂ K₂ hStar hns hK₂ hHK₂ hcases n hn
  · exfalso
    apply hnot
    rcases h with h | h | h
    · exact (sixModels_iff G).mpr (Or.inr (Or.inr (Or.inl h)))
    · exact (sixModels_iff G).mpr (Or.inl h)
    · exact (sixModels_iff G).mpr (Or.inr (Or.inl h))

end SzPS8

end CFSG.Quasithin
