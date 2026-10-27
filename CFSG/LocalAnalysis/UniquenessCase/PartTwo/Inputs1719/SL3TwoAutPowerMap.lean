module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSL3)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver)

@[expose] def K_SL3TwoAutPowerMap : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), IsSL3 Y n →
    Odd (Nat.card (Subgroup.center Y)) →
    ∀ S : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
      ∀ α : MulAut Y, (∃ k : ℕ, α ^ 2 ^ k = 1) → S.map α.toMonoidHom = S →
        (∀ P : Subgroup Y, IsMaxParabolicOver (⊤ : Subgroup Y) S P →
          P.map α.toMonoidHom = P) →
        ∃ j : ℕ, ∀ x ∈ Subgroup.normalizer (S : Set Y), α x * (x ^ 2 ^ j)⁻¹ ∈ S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
