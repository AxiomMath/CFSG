module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LieType.Universal CFSG.LieType.CurtisTits

section CT6'


def FF81_6_amalgam' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
    ∀ M : Subgroup G, FF81Conc5_7 b b₁ b₂ b₃ s₀ M → FF81Conc5_8 L t₀ →
    (∀ R : Subgroup G, R ≤ L → IsLnq 3 2 1 R → Subgroup.closure {β' b₂ b₃, s₀} ≤ R →
      IsLnq 3 2 1 (CenS R)) →
    ∃ Y : Subgroup G, HasLeviAmalgam F42 ↥Y ∧ Cen t₀ ≤ Y ∧ Cen s₀ ≤ Y ∧ Cen b ≤ Y ∧
      Cen (β' b₂ b₃) ≤ Y ∧ B ≤ Y ∧ Cen b ⊔ Cen (β' b₂ b₃) = Y

end CT6'

end CFSG.RankThree.PartTwo.Sec21.FF81
