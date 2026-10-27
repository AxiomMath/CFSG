module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_U4CartanPlus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n : ℕ), LieModel Y .PSU 4 2 n → 2 < 2 ^ n →
    ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 →
      p ∣ Nat.card (normalizerQuotient S)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
