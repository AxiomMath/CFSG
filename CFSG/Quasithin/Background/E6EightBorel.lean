module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.QuasithinUnique

@[expose] def E68BorelKernel : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (n : ℕ), 2 ≤ n →
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 2 n ∨
      CFSG.Blueprint.SuzukiModel (L ⧸ Subgroup.center L) 2 n ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 3 2 n) →
    IsPGroup 2 (Subgroup.center L) → ∀ S : Subgroup L, IsSylowTwoOf S ⊤ →
    ∀ p : ℕ, p.Prime → p ∣ 2 ^ n - 1 →
      padicValNat p (Nat.card (Subgroup.normalizer (S : Set L))) = padicValNat p (2 ^ n - 1)

end E6

end CFSG.Quasithin
