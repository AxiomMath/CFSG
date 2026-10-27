module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

@[expose] def K_BorelTorusAbelian : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f → LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ → IsMulCommutative (normalizerQuotient S)

@[expose] def K_CartanRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (t : CFSG.Open.StatedLieTag) (m f : ℕ),
    CFSG.Open.StatedLieAdmissible t m 2 f →
    LieModel (K ⧸ Subgroup.center K) t m 2 f →
    CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
    ∀ S : Subgroup K, IsSylowTwoOf S ⊤ →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ 2 ^ f - 1 →
        (t = .PSL → ¬ r ∣ m) → (t = .E6 → r ≠ 3) →
          CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t m ≤
            CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
