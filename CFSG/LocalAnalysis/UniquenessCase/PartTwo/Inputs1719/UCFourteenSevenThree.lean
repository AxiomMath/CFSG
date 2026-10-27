module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def UC2_14_7Three (D : Data G) : Prop :=
  ∀ (L : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (r p : ℕ) (A X B R : Subgroup G),
    Hyp8100 D L n r p A X → Case8100ThreeR D L p X →
      CFSG.ABGLocalTools.IsSylowOf r R X → Permutes R D.T →
      B ≤ D.M → Nat.card B = p → ⁅R, B⁆ = R → Permutes B D.T →
      UniqueMax D.M (B ⊔ R ⊔ D.T) ∧
        ∀ S : Subgroup G, S ≤ D.T →
          ((B ⊔ R ⊔ S : Subgroup G) : Set G) = (S : Set G) * (R : Set G) * (B : Set G) →
          CFSG.Open.pCoreOf 2 (B ⊔ R ⊔ S) ≠ ⊥ → UniqueMax D.M (B ⊔ R ⊔ S)

theorem uc2_14_7Three_of_evenRank_le_three (D : Data G) (h3 : CFSG.Open.evenRank G ≤ 3) :
    UC2_14_7Three D :=
  fun _ _ _ _ _ _ _ _ _ hc3 => absurd hc3.2.2.2.1 (by omega)

theorem case8100Three_of_p_eq_three {D : Data G} {L : Fin 2 → Subgroup G} {p : ℕ}
    {X : Subgroup G} (hp3 : p = 3) (hc : Case8100ThreeR D L p X ∨ Case8100FourR D L p X) :
    Case8100ThreeR D L p X :=
  hc.resolve_right fun h4 => by have := h4.2.2.1; omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
