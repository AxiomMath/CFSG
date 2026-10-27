module

public import CFSG.Walter.AStar
import CFSG.Walter.RankTwo
import CFSG.Walter.SimpleCaseStronglyEmbedded
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Walter

@[expose] def BenderHyp : Prop := ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
  (∃ a b : G, a * b ≠ b * a) → HasAbelianSylowTwo G → 3 ≤ CFSG.Open.twoRank G →
  (∀ H : Subgroup G, H ≠ ⊤ → IsAStar H) →
  IsTypeJR G ∨ ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M

theorem simpleCaseHyp_of_benderHyp
    (hB : BenderHyp) : SimpleCaseHyp := by
  intro L _ _ hsimple hnonab hab hA
  by_cases hr : CFSG.Open.twoRank L ≤ 2
  · exact Or.inl (isTypeL2_of_twoRank_le_two L hnonab hab hr)
  · rcases hB L hsimple hnonab hab (by omega) hA with hJR | ⟨M, hM⟩
    · exact Or.inr hJR
    · exact Or.inl (isTypeL2_of_stronglyEmbedded L hnonab hab M hM)

end CFSG.Walter
