module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergBYAschVanishing
import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.Assembly.InCatalog

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.GroupTheory.SteinbergBY

@[expose] def SelectedPrimeDichotomy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → evenRank G = 3 → sigmaA G ≠ {3} →
    AschCoreLocal G 2 ∨ ∃ p ∈ sigmaA G, 3 < p ∧ AschVanishing G p

@[expose] def VanishingRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    KProper InCatalog G → IsCharTwoType G → evenRank G = 3 →
    (∃ p ∈ sigmaA G, 3 < p ∧ AschVanishing G p) → IModel G

theorem part_one_outcome_of (hdich : SelectedPrimeDichotomy) (hrec : VanishingRecognition)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : KProper InCatalog G) (hchar : IsCharTwoType G) (he : evenRank G = 3)
    (hq : ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :
    IModel G ∨ AschCoreLocal G 2 := by
  have hsig : sigmaA G ≠ {3} :=
    (CFSG.RankThree.LocalRank.rank_three_selector_ne_three_iff he).2 hq
  rcases hdich G hnonab hK hchar he hsig with h | h
  · exact Or.inr h
  · exact Or.inl (hrec G hnonab hK hchar he h)

end CFSG.RankThree.PartOne
