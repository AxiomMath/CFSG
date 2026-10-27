module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R847ThinNe3 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 →
    Nat.card X = q → ∀ p ∈ D.sig, p ≠ 3 → normalizer (X : Set G) ≤ D.M

theorem normalizer_le_of_isSz_of_r847ThinNe3 {D : Data G} (h847 : R847ThinNe3 D) {p : ℕ}
    (hp : p ∈ D.sig) (hp3 : p ≠ 3) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) {A : Subgroup G} (hAL : A ≤ L) (hA : (Nat.card A).Prime)
    (hA2 : Nat.card A ≠ 2) : normalizer (A : Set G) ≤ D.M :=
  h847 L hL (PartTwo.S17.thin8_of_isSz hSz) A hAL _ hA hA2 rfl p hp hp3

end CFSG.LocalAnalysis.UniquenessCase.UC22
