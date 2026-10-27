module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def K_19_20_force : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Q : Type) [Group Q] (Y : Subgroup X),
    CFSG.Open.IsQuasisimple X → CFSG.pCore 2 X = ⊥ → Nonempty (Q ≃* X ⧸ center X) →
    (Shape19_16_124 X Y ∨ (IsLieTypeOver2 Q ∧ List19_16_5 Q ∧ IsNontrivialParabolic X Y)) →
    (∀ P : Subgroup X, IsPGroup 3 P → ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 →
      x * y = y * x) →
    ((∀ τ : MulAut X, τ ^ 3 = 1 → τ ∈ (MulAut.conj : X →* MulAut X).range) →
      center X = ⊥ →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ normalizer (S : Set X) ≤ Y) →
    (∃ Nn : Subgroup X, Nn ≤ Y ∧ (Nn.subgroupOf Y).Normal ∧ 3 ∣ Nat.card Nn ∧
      ∀ q : ℕ, q.Prime → q ∣ Nat.card Nn → q = 2 ∨ q = 3) →
    CFSG.Blueprint.LieModel X .PSL 3 2 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
